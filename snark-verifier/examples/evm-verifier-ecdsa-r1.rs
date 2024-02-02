use ethereum_types::Address;
use halo2_base::{
    halo2_proofs::{
        halo2curves::CurveAffine,
        poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK},
        {self},
    },
    utils::modulus,
    SKIP_FIRST_PASS,
};

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    halo2curves::bn256::{Bn256, Fq as bn256Fq, Fr, G1Affine},
    halo2curves::secp256r1::{Fp, Fq, Secp256r1Affine},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, Column, ConstraintSystem, Error,
        Instance, ProvingKey, VerifyingKey,
    },
    poly::{
        commitment::{Params, ParamsProver},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            strategy::AccumulatorStrategy,
        },
        VerificationStrategy,
    },
    transcript::{TranscriptReadBuffer, TranscriptWriterBuffer},
};
use itertools::Itertools;
use rand::rngs::OsRng;
use snark_verifier::{
    loader::evm::{
        encode_calldata, EvmLoader, ExecutorBuilder, {self},
    },
    pcs::kzg::{Bdfg21, Kzg},
    system::halo2::{compile, transcript::evm::EvmTranscript, Config},
    verifier::{
        PlonkVerifier, {self},
    },
};
use std::fmt::Write;
use std::fs::File;
use std::marker::PhantomData;
use std::rc::Rc;

use serde::{Deserialize, Serialize};

type Plonk = verifier::Plonk<Kzg<Bn256, Bdfg21>>;

use halo2_ecc::{
    ecc::{ecdsa::ecdsa_verify_no_pubkey_check, EccChip},
    fields::{
        fp::{FpConfig, FpStrategy},
        FieldChip, PrimeField,
    },
};

type FpChip<F> = FpConfig<F, Fp>;

#[derive(Serialize, Deserialize)]
struct CircuitParams {
    strategy: FpStrategy,
    degree: u32,
    num_advice: usize,
    num_lookup_advice: usize,
    num_fixed: usize,
    lookup_bits: usize,
    limb_bits: usize,
    num_limbs: usize,
}

#[derive(Clone, Copy)]
pub struct ECDSACircuit<F> {
    pub r: Option<Fq>,
    pub s: Option<Fq>,
    pub msghash: Option<Fq>,
    pub pk: Option<Secp256r1Affine>,
    pub g: Secp256r1Affine,
    pub _marker: PhantomData<F>,
}

impl<F: PrimeField> Default for ECDSACircuit<F> {
    fn default() -> Self {
        Self {
            r: None,
            s: None,
            msghash: None,
            pk: None,
            g: Secp256r1Affine::generator(),
            _marker: PhantomData,
        }
    }
}

#[derive(Clone)]
pub struct MyConfig<F: PrimeField> {
    fp_chip: FpChip<F>,
    instance: Column<Instance>,
}

#[derive(Clone)]
pub struct MyCircuit<F> {
    pub ecdsa: ECDSACircuit<F>,
    // pub msg: Option<Fq>,
    _f: PhantomData<F>,
}

impl<F> MyCircuit<F> {
    fn new(ecdsa: ECDSACircuit<F>) -> Self {
        //, msg: Option<Fq>) -> Self {
        Self {
            ecdsa,
            // msg,
            _f: PhantomData,
        }
    }
}

impl<F: PrimeField> Default for MyCircuit<F> {
    fn default() -> Self {
        Self {
            ecdsa: ECDSACircuit::<F>::default(),
            // msg : None,
            _f: PhantomData,
        }
    }
}

impl<F: PrimeField> Circuit<F> for MyCircuit<F> {
    type Config = MyConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // let path =
        //     var("ECDSA_CONFIG").unwrap_or_else(|_| "src/configs/ecdsa_circuit.config".to_string());
        let params: CircuitParams = CircuitParams {
            strategy: FpStrategy::Simple,
            degree: 17,
            num_advice: 4,
            num_lookup_advice: 1,
            num_fixed: 1,
            lookup_bits: 16,
            limb_bits: 88,
            num_limbs: 3,
        };
        // serde_json::from_reader(
        //     File::open(&path).unwrap_or_else(|_| panic!("{path:?} file should exist")),
        // )
        // .unwrap();

        let fp_chip = FpChip::<F>::configure(
            meta,
            params.strategy,
            &[params.num_advice],
            &[params.num_lookup_advice],
            params.num_fixed,
            params.lookup_bits,
            params.limb_bits,
            params.num_limbs,
            modulus::<Fp>(),
            0,
            params.degree as usize,
        );
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        Self::Config { fp_chip, instance }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.fp_chip.range.load_lookup_table(&mut layouter)?;

        let limb_bits = config.fp_chip.limb_bits;
        let num_limbs = config.fp_chip.num_limbs;
        let _num_fixed = config.fp_chip.range.gate.constants.len();
        let _lookup_bits = config.fp_chip.range.lookup_bits;
        let _num_advice = config.fp_chip.range.gate.num_advice;

        let mut first_pass = SKIP_FIRST_PASS;
        // ECDSA verify
        let out = layouter.assign_region(
            || "ECDSA",
            |region| {
                if first_pass {
                    first_pass = false;
                    return Ok(vec![]);
                }

                let mut aux = config.fp_chip.new_context(region);
                let ctx = &mut aux;

                let (r_assigned, s_assigned, m_assigned) = {
                    let fq_chip = FpConfig::<F, Fq>::construct(
                        config.fp_chip.range.clone(),
                        limb_bits,
                        num_limbs,
                        modulus::<Fq>(),
                    );

                    let m_assigned = fq_chip.load_private(
                        ctx,
                        FpConfig::<F, Fq>::fe_to_witness(
                            &self.ecdsa.msghash.map_or(Value::unknown(), Value::known),
                        ),
                    );

                    let r_assigned = fq_chip.load_private(
                        ctx,
                        FpConfig::<F, Fq>::fe_to_witness(
                            &self.ecdsa.r.map_or(Value::unknown(), Value::known),
                        ),
                    );
                    let s_assigned = fq_chip.load_private(
                        ctx,
                        FpConfig::<F, Fq>::fe_to_witness(
                            &self.ecdsa.s.map_or(Value::unknown(), Value::known),
                        ),
                    );

                    (r_assigned, s_assigned, m_assigned)
                };

                let ecc_chip = EccChip::<F, FpChip<F>>::construct(config.fp_chip.clone());
                let pk_assigned = ecc_chip.load_private(
                    ctx,
                    (
                        self.ecdsa.pk.map_or(Value::unknown(), |pt| Value::known(pt.x)),
                        self.ecdsa.pk.map_or(Value::unknown(), |pt| Value::known(pt.y)),
                    ),
                );
                // test ECDSA
                let _ecdsa = ecdsa_verify_no_pubkey_check::<F, Fp, Fq, Secp256r1Affine>(
                    &ecc_chip.field_chip,
                    ctx,
                    &pk_assigned,
                    &r_assigned,
                    &s_assigned,
                    &m_assigned,
                    4,
                    4,
                );

                // IMPORTANT: this copies cells to the lookup advice column to perform range check lookups
                // This is not optional.
                config.fp_chip.finalize(ctx);

                #[cfg(feature = "display")]
                if self.ecdsa.r.is_some() {
                    println!("ECDSA res {_ecdsa:?}");

                    // ctx.print_stats(&["Range"]);
                }
                // r_assigned.limbs().into_iter().map(|v| v.cell())
                // println!("{:?}", m_assigned.value);
                let out_cell = vec![_ecdsa.cell()];

                Ok(out_cell)
            },
        )?;
        // layouter.constrain_instance(out, config.instance, 0)?;
        for (i, cell) in out.into_iter().enumerate() {
            // println!("cell: {:?}, {:?}", i, cell);
            layouter.constrain_instance(cell, config.instance, i)?;
            // config.fp_chip.range.constrain_to_constant(&mut layouter, cell, self.msg[i])?;
        }
        Ok(())
    }
}

fn gen_srs(k: u32) -> ParamsKZG<Bn256> {
    ParamsKZG::<Bn256>::setup(k, OsRng)
}

fn gen_pk<C: Circuit<Fr>>(params: &ParamsKZG<Bn256>, circuit: &C) -> ProvingKey<G1Affine> {
    let vk = keygen_vk(params, circuit).unwrap();
    keygen_pk(params, vk, circuit).unwrap()
}

fn gen_proof<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
) -> Vec<u8> {
    MockProver::run(params.k(), &circuit, instances.clone()).unwrap().assert_satisfied_par();

    let instances = instances.iter().map(|instances| instances.as_slice()).collect_vec();
    let proof = {
        let mut transcript = TranscriptWriterBuffer::<_, G1Affine, _>::init(Vec::new());
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<_>,
            _,
            _,
            EvmTranscript<_, _, _, _>,
            _,
        >(params, pk, &[circuit], &[instances.as_slice()], OsRng, &mut transcript)
        .unwrap();
        transcript.finalize()
    };

    let accept = {
        let mut transcript = TranscriptReadBuffer::<_, G1Affine, _>::init(proof.as_slice());
        VerificationStrategy::<_, VerifierSHPLONK<_>>::finalize(
            verify_proof::<_, VerifierSHPLONK<_>, _, EvmTranscript<_, _, _, _>, _>(
                params.verifier_params(),
                pk.get_vk(),
                AccumulatorStrategy::new(params.verifier_params()),
                &[instances.as_slice()],
                &mut transcript,
            )
            .unwrap(),
        )
    };
    assert!(accept);

    proof
}

fn gen_evm_verifier(
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    num_instance: Vec<usize>,
) -> Result<(Vec<u8>, String), Error> {
    let svk = params.get_g()[0].into();
    let dk = (params.g2(), params.s_g2()).into();
    let protocol = compile(params, vk, Config::kzg().with_num_instance(num_instance.clone()));

    let loader = EvmLoader::new::<bn256Fq, Fr>();
    let protocol = protocol.loaded(&loader);

    let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(&loader);

    let instances = transcript.load_instances(num_instance);

    let proof = Plonk::read_proof(&svk, &protocol, &instances, &mut transcript);

    // println!("svk: {:?}", svk);
    // println!("dk: {:?}", svk);
    // println!("protocol {:?}", protocol);
    // println!("instances: {:?}", instances);
    // println!("proof {:?}", proof);

    Plonk::verify(&svk, &dk, &protocol, &instances, &proof);

    let yul_code: &String = &loader.yul_code();
    Ok((evm::compile_yul(yul_code), yul_code.clone()))
}

fn evm_verify(deployment_code: Vec<u8>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) -> bool {
    let calldata = encode_calldata(&instances, &proof);
    // println!("calldata: ");
    // for val in calldata.clone() {
    //     print!("{:02X}", val);
    // }

    let success = {
        let mut evm = ExecutorBuilder::default().with_gas_limit(u64::MAX.into()).build();

        let caller = Address::from_low_u64_be(0xfe);
        let verifier = evm.deploy(caller, deployment_code.into(), 0.into()).address.unwrap();
        let result = evm.call_raw(caller, verifier, calldata.into(), 0.into());
        //         println!("result: {:?}", result.out);
        //         println!("result: {:?}", result.reverted);
        //         println!("result: {:?}", result.env);
        //         println!("result: {:?}", result.env.tx.data);
        //         println!("data: ")
        // ;        for val in result.env.tx.data.clone() {
        //             print!("{:02X}", val);
        //         }

        dbg!(result.gas_used);
        println!("gas: {}", result.gas_used);

        !result.reverted
    };
    println!("res: {:?}", success);
    success
}

use regex::Regex;
use std::io::{BufRead, BufReader};
/// Reads in raw bytes code and generates equivalent .sol file
pub fn fix_verifier_sol(
    input_file: std::path::PathBuf,
) -> Result<String, Box<dyn std::error::Error>> {
    let file = std::fs::File::open(input_file.clone())?;
    let reader = BufReader::new(file);

    let mut transcript_addrs: Vec<u32> = Vec::new();
    let mut modified_lines: Vec<String> = Vec::new();

    // convert calldataload 0x0 to 0x40 to read from pubInputs, and the rest
    // from proof
    let calldata_pattern = Regex::new(r"^.*(calldataload\((0x[a-f0-9]+)\)).*$")?;
    let mstore_pattern = Regex::new(r"^\s*(mstore\(0x([0-9a-fA-F]+)+),.+\)")?;
    let mstore8_pattern = Regex::new(r"^\s*(mstore8\((\d+)+),.+\)")?;
    let mstoren_pattern = Regex::new(r"^\s*(mstore\((\d+)+),.+\)")?;
    let mload_pattern = Regex::new(r"(mload\((0x[0-9a-fA-F]+))\)")?;
    let keccak_pattern = Regex::new(r"(keccak256\((0x[0-9a-fA-F]+))")?;
    let modexp_pattern =
        Regex::new(r"(staticcall\(gas\(\), 0x5, (0x[0-9a-fA-F]+), 0xc0, (0x[0-9a-fA-F]+), 0x20)")?;
    let ecmul_pattern =
        Regex::new(r"(staticcall\(gas\(\), 0x7, (0x[0-9a-fA-F]+), 0x60, (0x[0-9a-fA-F]+), 0x40)")?;
    let ecadd_pattern =
        Regex::new(r"(staticcall\(gas\(\), 0x6, (0x[0-9a-fA-F]+), 0x80, (0x[0-9a-fA-F]+), 0x40)")?;
    let ecpairing_pattern =
        Regex::new(r"(staticcall\(gas\(\), 0x8, (0x[0-9a-fA-F]+), 0x180, (0x[0-9a-fA-F]+), 0x20)")?;
    let bool_pattern = Regex::new(r":bool")?;

    // Count the number of pub inputs
    let mut start = None;
    let mut end = None;
    for (i, line) in reader.lines().enumerate() {
        let line = line?;
        if line.trim().starts_with("mstore(0x20") {
            start = Some(i as u32);
        }

        if line.trim().starts_with("mstore(0x0") {
            end = Some(i as u32);
            break;
        }
    }

    let num_pubinputs = if let Some(s) = start { end.unwrap() - s } else { 0 };

    let mut max_pubinputs_addr = 0;
    if num_pubinputs > 0 {
        max_pubinputs_addr = num_pubinputs * 32 - 32;
    }

    let file = std::fs::File::open(input_file)?;
    let reader = BufReader::new(file);

    for line in reader.lines() {
        let mut line = line?;
        let m = bool_pattern.captures(&line);
        if m.is_some() {
            line = line.replace(":bool", "");
        }

        let m = calldata_pattern.captures(&line);
        if let Some(m) = m {
            let calldata_and_addr = m.get(1).unwrap().as_str();
            let addr = m.get(2).unwrap().as_str();
            let addr_as_num = u32::from_str_radix(addr.strip_prefix("0x").unwrap(), 16)?;

            if addr_as_num <= max_pubinputs_addr {
                let pub_addr = format!("{:#x}", addr_as_num + 32);
                line = line
                    .replace(calldata_and_addr, &format!("mload(add(pubInputs, {}))", pub_addr));
            } else {
                let proof_addr = format!("{:#x}", addr_as_num - max_pubinputs_addr);
                line =
                    line.replace(calldata_and_addr, &format!("mload(add(proof, {}))", proof_addr));
            }
        }

        let m = mstore8_pattern.captures(&line);
        if let Some(m) = m {
            let mstore = m.get(1).unwrap().as_str();
            let addr = m.get(2).unwrap().as_str();
            let addr_as_num = u32::from_str_radix(addr, 10)?;
            let transcript_addr = format!("{:#x}", addr_as_num);
            transcript_addrs.push(addr_as_num);
            line = line.replace(mstore, &format!("mstore8(add(transcript, {})", transcript_addr));
        }

        let m = mstoren_pattern.captures(&line);
        if let Some(m) = m {
            let mstore = m.get(1).unwrap().as_str();
            let addr = m.get(2).unwrap().as_str();
            let addr_as_num = u32::from_str_radix(addr, 10)?;
            let transcript_addr = format!("{:#x}", addr_as_num);
            transcript_addrs.push(addr_as_num);
            line = line.replace(mstore, &format!("mstore(add(transcript, {})", transcript_addr));
        }

        let m = modexp_pattern.captures(&line);
        if let Some(m) = m {
            let modexp = m.get(1).unwrap().as_str();
            let start_addr = m.get(2).unwrap().as_str();
            let result_addr = m.get(3).unwrap().as_str();
            let start_addr_as_num =
                u32::from_str_radix(start_addr.strip_prefix("0x").unwrap(), 16)?;
            let result_addr_as_num =
                u32::from_str_radix(result_addr.strip_prefix("0x").unwrap(), 16)?;

            let transcript_addr = format!("{:#x}", start_addr_as_num);
            transcript_addrs.push(start_addr_as_num);
            let result_addr = format!("{:#x}", result_addr_as_num);
            line = line.replace(
                modexp,
                &format!(
                    "staticcall(gas(), 0x5, add(transcript, {}), 0xc0, add(transcript, {}), 0x20",
                    transcript_addr, result_addr
                ),
            );
        }

        let m = ecmul_pattern.captures(&line);
        if let Some(m) = m {
            let ecmul = m.get(1).unwrap().as_str();
            let start_addr = m.get(2).unwrap().as_str();
            let result_addr = m.get(3).unwrap().as_str();
            let start_addr_as_num =
                u32::from_str_radix(start_addr.strip_prefix("0x").unwrap(), 16)?;
            let result_addr_as_num =
                u32::from_str_radix(result_addr.strip_prefix("0x").unwrap(), 16)?;

            let transcript_addr = format!("{:#x}", start_addr_as_num);
            let result_addr = format!("{:#x}", result_addr_as_num);
            transcript_addrs.push(start_addr_as_num);
            transcript_addrs.push(result_addr_as_num);
            line = line.replace(
                ecmul,
                &format!(
                    "staticcall(gas(), 0x7, add(transcript, {}), 0x60, add(transcript, {}), 0x40",
                    transcript_addr, result_addr
                ),
            );
        }

        let m = ecadd_pattern.captures(&line);
        if let Some(m) = m {
            let ecadd = m.get(1).unwrap().as_str();
            let start_addr = m.get(2).unwrap().as_str();
            let result_addr = m.get(3).unwrap().as_str();
            let start_addr_as_num =
                u32::from_str_radix(start_addr.strip_prefix("0x").unwrap(), 16)?;
            let result_addr_as_num =
                u32::from_str_radix(result_addr.strip_prefix("0x").unwrap(), 16)?;

            let transcript_addr = format!("{:#x}", start_addr_as_num);
            let result_addr = format!("{:#x}", result_addr_as_num);
            transcript_addrs.push(start_addr_as_num);
            transcript_addrs.push(result_addr_as_num);
            line = line.replace(
                ecadd,
                &format!(
                    "staticcall(gas(), 0x6, add(transcript, {}), 0x80, add(transcript, {}), 0x40",
                    transcript_addr, result_addr
                ),
            );
        }

        let m = ecpairing_pattern.captures(&line);
        if let Some(m) = m {
            let ecpairing = m.get(1).unwrap().as_str();
            let start_addr = m.get(2).unwrap().as_str();
            let result_addr = m.get(3).unwrap().as_str();
            let start_addr_as_num =
                u32::from_str_radix(start_addr.strip_prefix("0x").unwrap(), 16)?;
            let result_addr_as_num =
                u32::from_str_radix(result_addr.strip_prefix("0x").unwrap(), 16)?;

            let transcript_addr = format!("{:#x}", start_addr_as_num);
            let result_addr = format!("{:#x}", result_addr_as_num);
            transcript_addrs.push(start_addr_as_num);
            transcript_addrs.push(result_addr_as_num);
            line = line.replace(
                ecpairing,
                &format!(
                    "staticcall(gas(), 0x8, add(transcript, {}), 0x180, add(transcript, {}), 0x20",
                    transcript_addr, result_addr
                ),
            );
        }

        let m = mstore_pattern.captures(&line);
        if let Some(m) = m {
            let mstore = m.get(1).unwrap().as_str();
            let addr = m.get(2).unwrap().as_str();
            let addr_as_num = u32::from_str_radix(addr, 16)?;
            let transcript_addr = format!("{:#x}", addr_as_num);
            transcript_addrs.push(addr_as_num);
            line = line.replace(mstore, &format!("mstore(add(transcript, {})", transcript_addr));
        }

        let m = keccak_pattern.captures(&line);
        if let Some(m) = m {
            let keccak = m.get(1).unwrap().as_str();
            let addr = m.get(2).unwrap().as_str();
            let addr_as_num = u32::from_str_radix(addr.strip_prefix("0x").unwrap(), 16)?;
            let transcript_addr = format!("{:#x}", addr_as_num);
            transcript_addrs.push(addr_as_num);
            line = line.replace(keccak, &format!("keccak256(add(transcript, {})", transcript_addr));
        }

        // mload can show up multiple times per line
        loop {
            let m = mload_pattern.captures(&line);
            if m.is_none() {
                break;
            }
            let mload = m.as_ref().unwrap().get(1).unwrap().as_str();
            let addr = m.as_ref().unwrap().get(2).unwrap().as_str();

            let addr_as_num = u32::from_str_radix(addr.strip_prefix("0x").unwrap(), 16)?;
            let transcript_addr = format!("{:#x}", addr_as_num);
            transcript_addrs.push(addr_as_num);
            line = line.replace(mload, &format!("mload(add(transcript, {})", transcript_addr));
        }

        modified_lines.push(line);
    }

    // get the max transcript addr
    let max_transcript_addr = transcript_addrs.iter().max().unwrap() / 32;
    let mut contract = format!(
        "// SPDX-License-Identifier: MIT
    pragma solidity ^0.8.17;
    
    contract Verifier {{
        function verify(
            uint256[] memory pubInputs,
            bytes memory proof
        ) public view returns (bool) {{
            bool success = true;
            bytes32[{}] memory transcript;
            assembly {{
        ",
        max_transcript_addr
    )
    .trim()
    .to_string();

    // using a boxed Write trait object here to show it works for any Struct impl'ing Write
    // you may also use a std::fs::File here
    let write: Box<&mut dyn Write> = Box::new(&mut contract);

    for line in modified_lines[16..modified_lines.len() - 7].iter() {
        write!(write, "{}", line).unwrap();
    }
    writeln!(write, "}} return success; }} }}")?;
    Ok(contract)
}

fn main() {
    let params = gen_srs(17);
    use std::io::Write;
    // let circuit = StandardPlonk::rand(OsRng);
    let pk_x = [
        230, 252, 167, 67, 41, 160, 101, 125, 216, 243, 235, 213, 13, 202, 188, 117, 38, 51, 78,
        38, 45, 66, 151, 116, 152, 24, 17, 180, 222, 107, 247, 211,
    ];
    let pk_y = [
        99, 52, 101, 57, 10, 190, 48, 2, 38, 122, 193, 21, 54, 247, 49, 222, 163, 231, 11, 71, 147,
        23, 201, 95, 30, 160, 209, 48, 215, 43, 204, 100,
    ];
    let pubkey_point =
        Secp256r1Affine::from_xy(Fp::from_bytes(&pk_x).unwrap(), Fp::from_bytes(&pk_y).unwrap())
            .into();
    let r = [
        109, 7, 241, 37, 255, 21, 158, 18, 158, 54, 130, 103, 125, 166, 123, 136, 203, 171, 59,
        183, 71, 148, 86, 50, 96, 101, 3, 1, 167, 197, 190, 227,
    ];
    let r_point = <Secp256r1Affine as CurveAffine>::ScalarExt::from_bytes(&r).into();
    let s = [
        64, 195, 207, 129, 70, 2, 111, 190, 69, 117, 75, 166, 202, 197, 124, 243, 84, 55, 13, 129,
        89, 222, 45, 201, 38, 240, 215, 234, 148, 9, 140, 102,
    ];
    let s_point = <Secp256r1Affine as CurveAffine>::ScalarExt::from_bytes(&s).into();

    let msghash = [
        164, 189, 198, 187, 56, 76, 105, 243, 217, 0, 253, 20, 230, 233, 26, 16, 176, 221, 70, 240,
        17, 133, 45, 140, 148, 229, 134, 37, 147, 135, 82, 241,
    ];
    let msghash_point = <Secp256r1Affine as CurveAffine>::ScalarExt::from_bytes(&msghash).into();

    // let m_fes = msghash.iter().map(|v| Fr::from(*v as u64)).collect::<Vec<Fr>>();

    // println!("msghash: {:?}", m_fes.clone());

    let g = Secp256r1Affine::generator();

    let ecdsa_circuit = ECDSACircuit::<Fr> {
        r: r_point,
        s: s_point,
        msghash: msghash_point,
        pk: pubkey_point,
        g,
        _marker: PhantomData,
    };

    let circuit = MyCircuit::<Fr>::new(ecdsa_circuit); //, <Secp256r1Affine as CurveAffine>::ScalarExt::from_bytes(&msghash).into());
    let pk = gen_pk(&params, &circuit);
    let (deployment_code, yul_code) = gen_evm_verifier(&params, pk.get_vk(), vec![1]).unwrap();
    let yul_code_path = std::path::PathBuf::from("./YulCode.yul");

    let mut f = std::fs::File::create(yul_code_path.clone()).unwrap();
    let _ = f.write(yul_code.as_bytes());

    let output = fix_verifier_sol(yul_code_path).unwrap();
    // println!("{}", output);

    let sol_code_path = std::path::PathBuf::from("./Verifier.sol");
    let mut f = File::create(sol_code_path).unwrap();
    let _ = f.write(output.as_bytes());
    // println!("{:?}", circuit.instances() );
    let proof = gen_proof(&params, &pk, circuit.clone(), vec![vec![1.into()]]);

    // println!("proof: ");
    // for val in proof.clone() {
    //     print!("{:02X}", val);
    // }
    let hex_string: String = proof.iter().map(|b| format!("{:02x}", b)).collect();

    let proof_path = std::path::PathBuf::from("./proof.out");
    let mut f = File::create(proof_path).unwrap();
    let _ = f.write(hex_string.as_bytes());

    // println!("deployment_code: ");
    // for val in deployment_code.clone() {
    //     print!("{:02X}", val);
    // }

    let res = evm_verify(deployment_code.clone(), vec![vec![1.into()]], proof);
    assert!(res)
}
