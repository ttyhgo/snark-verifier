use crate::{
    cost::{Cost, CostEstimation},
    loader::{native::NativeLoader, LoadedScalar, Loader},
    pcs::{
        AccumulatorEncoding, MultiOpenScheme, {self},
    },
    util::{
        arithmetic::{CurveAffine, Field, Rotation},
        msm::Msm,
        protocol::{
            CommonPolynomial::Lagrange, CommonPolynomialEvaluation, LinearizationStrategy, Query,
        },
        transcript::TranscriptRead,
        Itertools,
    },
    verifier::PlonkVerifier,
    Error, Protocol,
};
use rustc_hash::FxHashMap;
use std::{iter, marker::PhantomData};

pub struct Plonk<MOS, AE = ()>(PhantomData<(MOS, AE)>);

impl<C, L, MOS, AE> PlonkVerifier<C, L, MOS> for Plonk<MOS, AE>
where
    C: CurveAffine,
    L: Loader<C>,
    MOS: MultiOpenScheme<C, L>,
    AE: AccumulatorEncoding<C, L, MOS>,
{
    type Proof = PlonkProof<C, L, MOS>;

    fn read_proof<T>(
        svk: &MOS::SuccinctVerifyingKey,
        protocol: &Protocol<C, L>,
        instances: &[Vec<L::LoadedScalar>],
        transcript: &mut T,
    ) -> Self::Proof
    where
        T: TranscriptRead<C, L>,
    {
        PlonkProof::read::<T, AE>(svk, protocol, instances, transcript)
    }

    fn succinct_verify(
        svk: &MOS::SuccinctVerifyingKey,
        protocol: &Protocol<C, L>,
        instances: &[Vec<L::LoadedScalar>],
        proof: &Self::Proof,
    ) -> Vec<MOS::Accumulator> {
        let common_poly_eval = {
            let mut common_poly_eval = CommonPolynomialEvaluation::new(
                &protocol.domain,
                lagranges(protocol, instances),
                &proof.z,
            );

            L::batch_invert(common_poly_eval.denoms());
            common_poly_eval.evaluate();

            common_poly_eval
        };

        let mut evaluations = proof.evaluations(protocol, instances, &common_poly_eval);
        let commitments = proof.commitments(protocol, &common_poly_eval, &mut evaluations);
        let queries = proof.queries(protocol, evaluations);

        let accumulator = MOS::succinct_verify(svk, &commitments, &proof.z, &queries, &proof.pcs);

        let accumulators = iter::empty()
            .chain(Some(accumulator))
            .chain(proof.old_accumulators.iter().cloned())
            .collect();

        accumulators
    }
}

#[derive(Clone, Debug)]
pub struct PlonkProof<C, L, MOS>
where
    C: CurveAffine,
    L: Loader<C>,
    MOS: MultiOpenScheme<C, L>,
{
    pub committed_instances: Option<Vec<L::LoadedEcPoint>>,
    pub witnesses: Vec<L::LoadedEcPoint>,
    pub challenges: Vec<L::LoadedScalar>,
    pub quotients: Vec<L::LoadedEcPoint>,
    pub z: L::LoadedScalar,
    pub evaluations: Vec<L::LoadedScalar>,
    pub pcs: MOS::Proof,
    pub old_accumulators: Vec<MOS::Accumulator>,
}

impl<C, L, MOS> PlonkProof<C, L, MOS>
where
    C: CurveAffine,
    L: Loader<C>,
    MOS: MultiOpenScheme<C, L>,
{
    pub fn read<T, AE>(
        svk: &MOS::SuccinctVerifyingKey,
        protocol: &Protocol<C, L>,
        instances: &[Vec<L::LoadedScalar>],
        transcript: &mut T,
    ) -> Self
    where
        T: TranscriptRead<C, L>,
        AE: AccumulatorEncoding<C, L, MOS>,
    {
        if let Some(transcript_initial_state) = &protocol.transcript_initial_state {
            transcript.common_scalar(transcript_initial_state).unwrap();
        }

        debug_assert_eq!(
            protocol.num_instance,
            instances.iter().map(|instances| instances.len()).collect_vec(),
            "Invalid Instances"
        );

        let committed_instances = if let Some(ick) = &protocol.instance_committing_key {
            let loader = transcript.loader();
            let bases =
                ick.bases.iter().map(|value| loader.ec_point_load_const(value)).collect_vec();
            let constant = ick.constant.as_ref().map(|value| loader.ec_point_load_const(value));

            let committed_instances = instances
                .iter()
                .map(|instances| {
                    instances
                        .iter()
                        .zip(bases.iter())
                        .map(|(scalar, base)| Msm::<C, L>::base(base) * scalar)
                        .chain(constant.as_ref().map(Msm::base))
                        .sum::<Msm<_, _>>()
                        .evaluate(None)
                })
                .collect_vec();
            for committed_instance in committed_instances.iter() {
                transcript.common_ec_point(committed_instance).unwrap();
            }

            Some(committed_instances)
        } else {
            for instances in instances.iter() {
                for instance in instances.iter() {
                    transcript.common_scalar(instance).unwrap();
                }
            }

            None
        };

        let (witnesses, challenges) = {
            let (witnesses, challenges): (Vec<_>, Vec<_>) = protocol
                .num_witness
                .iter()
                .zip(protocol.num_challenge.iter())
                .map(|(&n, &m)| {
                    (transcript.read_n_ec_points(n).unwrap(), transcript.squeeze_n_challenges(m))
                })
                .unzip();

            (
                witnesses.into_iter().flatten().collect_vec(),
                challenges.into_iter().flatten().collect_vec(),
            )
        };

        let quotients = transcript.read_n_ec_points(protocol.quotient.num_chunk()).unwrap();

        let z = transcript.squeeze_challenge();
        let evaluations = transcript.read_n_scalars(protocol.evaluations.len()).unwrap();

        let pcs = MOS::read_proof(svk, &Self::empty_queries(protocol), transcript);

        let old_accumulators = protocol
            .accumulator_indices
            .iter()
            .map(|accumulator_indices| {
                AE::from_repr(
                    &accumulator_indices.iter().map(|&(i, j)| &instances[i][j]).collect_vec(),
                )
                .unwrap()
            })
            .collect_vec();

        Self {
            committed_instances,
            witnesses,
            challenges,
            quotients,
            z,
            evaluations,
            pcs,
            old_accumulators,
        }
    }

    pub fn empty_queries(protocol: &Protocol<C, L>) -> Vec<pcs::Query<C::Scalar>> {
        protocol
            .queries
            .iter()
            .map(|query| pcs::Query {
                poly: query.poly,
                shift: protocol.domain.rotate_scalar(C::Scalar::ONE, query.rotation),
                eval: (),
            })
            .collect()
    }

    fn queries(
        &self,
        protocol: &Protocol<C, L>,
        mut evaluations: FxHashMap<Query, L::LoadedScalar>,
    ) -> Vec<pcs::Query<C::Scalar, L::LoadedScalar>> {
        Self::empty_queries(protocol)
            .into_iter()
            .zip(protocol.queries.iter().map(|query| evaluations.remove(query).unwrap()))
            .map(|(query, eval)| query.with_evaluation(eval))
            .collect()
    }

    fn commitments<'a>(
        &'a self,
        protocol: &'a Protocol<C, L>,
        common_poly_eval: &CommonPolynomialEvaluation<C, L>,
        evaluations: &mut FxHashMap<Query, L::LoadedScalar>,
    ) -> Vec<Msm<C, L>> {
        let loader = common_poly_eval.zn().loader();
        let mut commitments = iter::empty()
            .chain(protocol.preprocessed.iter().map(Msm::base))
            .chain(
                self.committed_instances
                    .as_ref()
                    .map(|committed_instances| {
                        committed_instances.iter().map(Msm::base).collect_vec()
                    })
                    .unwrap_or_else(|| {
                        iter::repeat_with(Default::default)
                            .take(protocol.num_instance.len())
                            .collect_vec()
                    }),
            )
            .chain(self.witnesses.iter().map(Msm::base))
            .collect_vec();

        let numerator = protocol.quotient.numerator.evaluate(
            &|scalar| Msm::constant(loader.load_const(&scalar)),
            &|poly| Msm::constant(common_poly_eval.get(poly).clone()),
            &|query| {
                evaluations
                    .get(&query)
                    .cloned()
                    .map(Msm::constant)
                    .or_else(|| {
                        (query.rotation == Rotation::cur())
                            .then(|| commitments.get(query.poly).cloned())
                            .flatten()
                    })
                    .ok_or(Error::InvalidQuery(query))
                    .unwrap()
            },
            &|index| {
                self.challenges
                    .get(index)
                    .cloned()
                    .map(Msm::constant)
                    .ok_or(Error::InvalidChallenge(index))
                    .unwrap()
            },
            &|a| -a,
            &|a, b| a + b,
            &|a, b| match (a.size(), b.size()) {
                (0, _) => b * &a.try_into_constant().unwrap(),
                (_, 0) => a * &b.try_into_constant().unwrap(),
                (_, _) => panic!("{:?}", Error::InvalidLinearization),
            },
            &|a, scalar| a * &loader.load_const(&scalar),
        );

        let quotient_query = Query::new(
            protocol.preprocessed.len() + protocol.num_instance.len() + self.witnesses.len(),
            Rotation::cur(),
        );
        let quotient = common_poly_eval
            .zn()
            .pow_const(protocol.quotient.chunk_degree as u64)
            .powers(self.quotients.len())
            .into_iter()
            .zip(self.quotients.iter().map(Msm::base))
            .map(|(coeff, chunk)| chunk * &coeff)
            .sum::<Msm<_, _>>();
        match protocol.linearization {
            Some(LinearizationStrategy::WithoutConstant) => {
                let linearization_query = Query::new(quotient_query.poly + 1, Rotation::cur());
                let (msm, constant) = numerator.split();
                commitments.push(quotient);
                commitments.push(msm);
                evaluations.insert(
                    quotient_query,
                    (constant.unwrap_or_else(|| loader.load_zero())
                        + evaluations.get(&linearization_query).unwrap())
                        * common_poly_eval.zn_minus_one_inv(),
                );
            }
            Some(LinearizationStrategy::MinusVanishingTimesQuotient) => {
                let (msm, constant) =
                    (numerator - quotient * common_poly_eval.zn_minus_one()).split();
                commitments.push(msm);
                evaluations.insert(quotient_query, constant.unwrap_or_else(|| loader.load_zero()));
            }
            None => {
                commitments.push(quotient);
                evaluations.insert(
                    quotient_query,
                    numerator.try_into_constant().ok_or(Error::InvalidLinearization).unwrap()
                        * common_poly_eval.zn_minus_one_inv(),
                );
            }
        }

        commitments
    }

    fn evaluations(
        &self,
        protocol: &Protocol<C, L>,
        instances: &[Vec<L::LoadedScalar>],
        common_poly_eval: &CommonPolynomialEvaluation<C, L>,
    ) -> FxHashMap<Query, L::LoadedScalar> {
        let loader = common_poly_eval.zn().loader();
        let instance_evals = protocol.instance_committing_key.is_none().then(|| {
            let offset = protocol.preprocessed.len();
            let queries = {
                let range = offset..offset + protocol.num_instance.len();
                protocol
                    .quotient
                    .numerator
                    .used_query()
                    .into_iter()
                    .filter(move |query| range.contains(&query.poly))
            };
            queries
                .map(move |query| {
                    let instances = instances[query.poly - offset].iter();
                    let l_i_minus_r = (-query.rotation.0..)
                        .map(|i_minus_r| common_poly_eval.get(Lagrange(i_minus_r)));
                    let eval = loader.sum_products(&instances.zip(l_i_minus_r).collect_vec());
                    (query, eval)
                })
                .collect_vec()
        });

        iter::empty()
            .chain(instance_evals.into_iter().flatten())
            .chain(protocol.evaluations.iter().cloned().zip(self.evaluations.iter().cloned()))
            .collect()
    }
}

impl<C, MOS> CostEstimation<(C, MOS)> for Plonk<MOS>
where
    C: CurveAffine,
    MOS: MultiOpenScheme<C, NativeLoader> + CostEstimation<C, Input = Vec<pcs::Query<C::Scalar>>>,
{
    type Input = Protocol<C>;

    fn estimate_cost(protocol: &Protocol<C>) -> Cost {
        let plonk_cost = {
            let num_accumulator = protocol.accumulator_indices.len();
            let num_instance = protocol.num_instance.iter().sum();
            let num_commitment =
                protocol.num_witness.iter().sum::<usize>() + protocol.quotient.num_chunk();
            let num_evaluation = protocol.evaluations.len();
            let num_msm = protocol.preprocessed.len() + num_commitment + 1 + 2 * num_accumulator;
            Cost::new(num_instance, num_commitment, num_evaluation, num_msm)
        };
        let pcs_cost = {
            let queries = PlonkProof::<C, NativeLoader, MOS>::empty_queries(protocol);
            MOS::estimate_cost(&queries)
        };
        plonk_cost + pcs_cost
    }
}

fn lagranges<C, L>(
    protocol: &Protocol<C, L>,
    instances: &[Vec<L::LoadedScalar>],
) -> impl IntoIterator<Item = i32>
where
    C: CurveAffine,
    L: Loader<C>,
{
    let instance_eval_lagrange = protocol.instance_committing_key.is_none().then(|| {
        let queries = {
            let offset = protocol.preprocessed.len();
            let range = offset..offset + protocol.num_instance.len();
            protocol
                .quotient
                .numerator
                .used_query()
                .into_iter()
                .filter(move |query| range.contains(&query.poly))
        };
        let (min_rotation, max_rotation) = queries.fold((0, 0), |(min, max), query| {
            if query.rotation.0 < min {
                (query.rotation.0, max)
            } else if query.rotation.0 > max {
                (min, query.rotation.0)
            } else {
                (min, max)
            }
        });
        let max_instance_len =
            Iterator::max(instances.iter().map(|instance| instance.len())).unwrap_or_default();
        -max_rotation..max_instance_len as i32 + min_rotation.abs()
    });
    protocol
        .quotient
        .numerator
        .used_langrange()
        .into_iter()
        .chain(instance_eval_lagrange.into_iter().flatten())
}
