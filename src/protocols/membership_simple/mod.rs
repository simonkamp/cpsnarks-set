//! Implements CPMemRSA and CPMemRSAPrm.
use crate::{
    commitments::{integer::IntegerCommitment, pedersen::PedersenCommitment, Commitment},
    parameters::Parameters,
    protocols::{
        modeq::{
            channel::{ModEqProverChannel, ModEqVerifierChannel},
            CRSModEq, Proof as ModEqProof, Protocol as ModEqProtocol, Statement as ModEqStatement,
            Witness as ModEqWitness,
        },
        root::{
            channel::{RootProverChannel, RootVerifierChannel},
            CRSRoot, Proof as RootProof, Protocol as RootProtocol, Statement as RootStatement,
            Witness as RootWitness,
        },
        ProofError, SetupError, VerificationError,
    },
    utils::ConvertibleUnknownOrderGroup,
    utils::{curve::CurvePointProjective, random_between},
};
use channel::{MembershipProverChannel, MembershipVerifierChannel};
use rand::{CryptoRng, RngCore};
use rug::rand::MutRandState;
use rug::Integer;

pub mod channel;
pub mod transcript;

pub struct CRS<G: ConvertibleUnknownOrderGroup, P: CurvePointProjective>
{
    // G contains the information about Z^*_N
    pub parameters: Parameters,
    pub crs_root: CRSRoot<G>,
    pub crs_modeq: CRSModEq<G, P>,
}

impl<G: ConvertibleUnknownOrderGroup, P: CurvePointProjective> Clone
    for CRS<G, P>
{
    fn clone(&self) -> Self {
        Self {
            parameters: self.parameters.clone(),
            crs_root: self.crs_root.clone(),
            crs_modeq: self.crs_modeq.clone(),
        }
    }
}

pub struct Protocol<
    G: ConvertibleUnknownOrderGroup,
    P: CurvePointProjective,

> {
    pub crs: CRS<G, P>,
}

pub struct Statement<G: ConvertibleUnknownOrderGroup, P: CurvePointProjective> {
    pub c_p: G::Elem,
    pub c_e_q: <PedersenCommitment<P> as Commitment>::Instance,
}

pub struct Witness<G: ConvertibleUnknownOrderGroup> {
    pub e: Integer,
    pub r_q: Integer,
    pub w: G::Elem,
}

pub struct Proof<
    G: ConvertibleUnknownOrderGroup,
    P: CurvePointProjective,

> {
    pub c_e: <IntegerCommitment<G> as Commitment>::Instance,
    pub proof_root: RootProof<G>,
    pub proof_modeq: ModEqProof<G, P>,
}

impl<G: ConvertibleUnknownOrderGroup, P: CurvePointProjective> Clone
    for Proof<G, P>
{
    fn clone(&self) -> Self {
        Self {
            c_e: self.c_e.clone(),
            proof_root: self.proof_root.clone(),
            proof_modeq: self.proof_modeq.clone(),
        }
    }
}

impl<G: ConvertibleUnknownOrderGroup, P: CurvePointProjective>
    Protocol<G, P>
{
    pub fn setup<R1: MutRandState, R2: RngCore + CryptoRng>(
        parameters: &Parameters,
        rng1: &mut R1,
        rng2: &mut R2,
    ) -> Result<Protocol<G, P>, SetupError> {
        let integer_commitment_parameters = IntegerCommitment::<G>::setup(rng1);
        let pedersen_commitment_parameters = PedersenCommitment::<P>::setup(rng2);

        Ok(Protocol {
            crs: CRS::<G, P> {
                parameters: parameters.clone(),
                crs_modeq: CRSModEq::<G, P> {
                    parameters: parameters.clone(),
                    integer_commitment_parameters: integer_commitment_parameters.clone(),
                    pedersen_commitment_parameters: pedersen_commitment_parameters.clone(),
                },
                crs_root: CRSRoot::<G> {
                    parameters: parameters.clone(),
                    integer_commitment_parameters,
                },
            },
        })
    }

    pub fn prove<
        R1: MutRandState,
        R2: RngCore + CryptoRng,
        C: MembershipVerifierChannel<G>
            + RootVerifierChannel<G>
            + ModEqVerifierChannel<G, P>
    >(
        &self,
        verifier_channel: &mut C,
        rng1: &mut R1,
        rng2: &mut R2,
        statement: &Statement<G, P>,
        witness: &Witness<G>,
    ) -> Result<(), ProofError> {
        let r = random_between(rng1, &Integer::from(0), &G::order_upper_bound());
        let c_e = self
            .crs
            .crs_root
            .integer_commitment_parameters
            .commit(&witness.e, &r)?;
        verifier_channel.send_c_e(&c_e)?;
        let root = RootProtocol::from_crs(&self.crs.crs_root);
        root.prove(
            verifier_channel,
            rng1,
            &RootStatement {
                c_e: c_e.clone(),
                acc: statement.c_p.clone(),
            },
            &RootWitness {
                e: witness.e.clone(),
                r: r.clone(),
                w: witness.w.clone(),
            },
        )?;
        let modeq = ModEqProtocol::from_crs(&self.crs.crs_modeq);
        modeq.prove(
            verifier_channel,
            rng1,
            rng2,
            &ModEqStatement {
                c_e,
                c_e_q: statement.c_e_q.clone(),
            },
            &ModEqWitness {
                e: witness.e.clone(),
                r,
                r_q: witness.r_q.clone(),
            },
        )?;

        Ok(())
    }

    pub fn verify<
        C: MembershipProverChannel<G>
            + RootProverChannel<G>
            + ModEqProverChannel<G, P>
    >(
        &self,
        prover_channel: &mut C,
        statement: &Statement<G, P>,
    ) -> Result<(), VerificationError> {
        let c_e = prover_channel.receive_c_e()?;
        let root = RootProtocol::from_crs(&self.crs.crs_root);
        root.verify(
            prover_channel,
            &RootStatement {
                c_e: c_e.clone(),
                acc: statement.c_p.clone(),
            },
        )?;
        let modeq = ModEqProtocol::from_crs(&self.crs.crs_modeq);
        modeq.verify(
            prover_channel,
            &ModEqStatement {
                c_e,
                c_e_q: statement.c_e_q.clone(),
            },
        )?;


        Ok(())
    }



    pub fn from_crs(crs: &CRS<G, P>) -> Protocol<G, P> {
        Protocol { crs: crs.clone() }
    }
}

#[cfg(all(test, feature = "zexe"))]
mod test {
    use super::{Protocol, Statement, Witness};
    use crate::{
        commitments::Commitment,
        parameters::Parameters,
        protocols::hash_to_prime::snark_range::Protocol as HPProtocol,
        protocols::{
            hash_to_prime::snark_hash::{HashToPrimeHashParameters, Protocol as HPHashProtocol},
            membership::transcript::{TranscriptProverChannel, TranscriptVerifierChannel},
        },
    };
    use accumulator::group::{ClassGroup, Rsa2048};
    use accumulator::{group::Group, AccumulatorWithoutHashToPrime};
    use algebra::bls12_381::{Bls12_381, G1Projective};
    use merlin::Transcript;
    use rand::thread_rng;
    use rug::rand::RandState;
    use rug::Integer;
    use std::cell::RefCell;

    const LARGE_PRIMES: [u64; 4] = [
        553_525_575_239_331_913,
        12_702_637_924_034_044_211,
        378_373_571_372_703_133,
        8_640_171_141_336_142_787,
    ];

    #[test]
    fn test_e2e_prime_rsa() {
        let params = Parameters::from_security_level(128).unwrap();
        let mut rng1 = RandState::new();
        rng1.seed(&Integer::from(13));
        let mut rng2 = thread_rng();

        let crs = crate::protocols::membership::Protocol::<
            Rsa2048,
            G1Projective,
            HPProtocol<Bls12_381>,
        >::setup(&params, &mut rng1, &mut rng2)
        .unwrap()
        .crs;
        let protocol = Protocol::<Rsa2048, G1ProjectiveProtocol<Bls12_381>>::from_crs(&crs);

        let value = Integer::from(Integer::u_pow_u(
            2,
            (crs.parameters.hash_to_prime_bits) as u32,
        )) - &Integer::from(245);
        let randomness = Integer::from(5);
        let commitment = protocol
            .crs
            .crs_modeq
            .pedersen_commitment_parameters
            .commit(&value, &randomness)
            .unwrap();

        let accum =
            accumulator::Accumulator::<Rsa2048, Integer, AccumulatorWithoutHashToPrime>::empty();
        let accum = accum.add(
            &LARGE_PRIMES
                .iter()
                .skip(1)
                .map(|p| Integer::from(*p))
                .collect::<Vec<_>>(),
        );

        let accum = accum.add_with_proof(&[value.clone()]);
        let acc = accum.0.value;
        let w = accum.1.witness.0.value;
        assert_eq!(Rsa2048::exp(&w, &value), acc);

        let proof_transcript = RefCell::new(Transcript::new(b"membership"));
        let mut verifier_channel = TranscriptVerifierChannel::new(&crs, &proof_transcript);
        let statement = Statement {
            c_e_q: commitment,
            c_p: acc,
        };
        protocol
            .prove(
                &mut verifier_channel,
                &mut rng1,
                &mut rng2,
                &statement,
                &Witness {
                    e: value,
                    r_q: randomness,
                    w,
                },
            )
            .unwrap();
        let proof = verifier_channel.proof().unwrap();
        let verification_transcript = RefCell::new(Transcript::new(b"membership"));
        let mut prover_channel =
            TranscriptProverChannel::new(&crs, &verification_transcript, &proof);
        protocol.verify(&mut prover_channel, &statement).unwrap();
    }

    #[test]
    fn test_e2e_prime_class_group() {
        let params = Parameters::from_security_level(128).unwrap();
        let mut rng1 = RandState::new();
        rng1.seed(&Integer::from(13));
        let mut rng2 = thread_rng();

        let crs = crate::protocols::membership::Protocol::<
            ClassGroup,
            G1Projective,
            HPProtocol<Bls12_381>,
        >::setup(&params, &mut rng1, &mut rng2)
        .unwrap()
        .crs;
        let protocol = Protocol::<ClassGroup, G1ProjectiveProtocol<Bls12_381>>::from_crs(&crs);

        let value = Integer::from(Integer::u_pow_u(
            2,
            (crs.parameters.hash_to_prime_bits) as u32,
        )) - &Integer::from(245);
        let randomness = Integer::from(5);
        let commitment = protocol
            .crs
            .crs_modeq
            .pedersen_commitment_parameters
            .commit(&value, &randomness)
            .unwrap();

        let accum =
            accumulator::Accumulator::<ClassGroup, Integer, AccumulatorWithoutHashToPrime>::empty();
        let accum = accum.add(
            &LARGE_PRIMES
                .iter()
                .skip(1)
                .map(|p| Integer::from(*p))
                .collect::<Vec<_>>(),
        );

        let accum = accum.add_with_proof(&[value.clone()]);
        let acc = accum.0.value;
        let w = accum.1.witness.0.value;
        assert_eq!(ClassGroup::exp(&w, &value), acc);

        let proof_transcript = RefCell::new(Transcript::new(b"membership"));
        let mut verifier_channel = TranscriptVerifierChannel::new(&crs, &proof_transcript);
        let statement = Statement {
            c_e_q: commitment,
            c_p: acc,
        };
        protocol
            .prove(
                &mut verifier_channel,
                &mut rng1,
                &mut rng2,
                &statement,
                &Witness {
                    e: value,
                    r_q: randomness,
                    w,
                },
            )
            .unwrap();
        let proof = verifier_channel.proof().unwrap();
        let verification_transcript = RefCell::new(Transcript::new(b"membership"));
        let mut prover_channel =
            TranscriptProverChannel::new(&crs, &verification_transcript, &proof);
        protocol.verify(&mut prover_channel, &statement).unwrap();
    }

    #[test]
    fn test_e2e_hash_to_prime() {
        struct TestHashToPrimeParameters {}
        impl HashToPrimeHashParameters for TestHashToPrimeParameters {
            const MESSAGE_SIZE: u16 = 254;
        }

        let params = Parameters::from_security_level(128).unwrap();
        let mut rng1 = RandState::new();
        rng1.seed(&Integer::from(13));
        let mut rng2 = thread_rng();

        let crs = crate::protocols::membership::Protocol::<
            Rsa2048,
            G1Projective,
            HPHashProtocol<Bls12_381, TestHashToPrimeParameters>,
        >::setup(&params, &mut rng1, &mut rng2)
        .unwrap()
        .crs;
        let protocol = Protocol::<
            Rsa2048,
            G1Projective,
            HPHashProtocol<Bls12_381, TestHashToPrimeParameters>,
        >::from_crs(&crs);

        let value = Integer::from(24_928_329);
        let (hashed_value, _) = protocol.hash_to_prime(&value).unwrap();
        let randomness = Integer::from(5);
        let commitment = protocol
            .crs
            .crs_modeq
            .pedersen_commitment_parameters
            .commit(&hashed_value, &randomness)
            .unwrap();

        let accum =
            accumulator::Accumulator::<Rsa2048, Integer, AccumulatorWithoutHashToPrime>::empty();
        let accum = accum.add(
            &LARGE_PRIMES
                .iter()
                .skip(1)
                .map(|p| Integer::from(*p))
                .collect::<Vec<_>>(),
        );

        let accum = accum.add_with_proof(&[hashed_value.clone()]);
        let acc = accum.0.value;
        let w = accum.1.witness.0.value;
        assert_eq!(Rsa2048::exp(&w, &hashed_value), acc);

        let proof_transcript = RefCell::new(Transcript::new(b"membership"));
        let mut verifier_channel = TranscriptVerifierChannel::new(&crs, &proof_transcript);
        let statement = Statement {
            c_e_q: commitment,
            c_p: acc,
        };
        protocol
            .prove(
                &mut verifier_channel,
                &mut rng1,
                &mut rng2,
                &statement,
                &Witness {
                    e: value,
                    r_q: randomness,
                    w,
                },
            )
            .unwrap();
        let proof = verifier_channel.proof().unwrap();
        let verification_transcript = RefCell::new(Transcript::new(b"membership"));
        let mut prover_channel =
            TranscriptProverChannel::new(&crs, &verification_transcript, &proof);
        protocol.verify(&mut prover_channel, &statement).unwrap();
    }
}

#[cfg(all(test, feature = "dalek"))]
mod test {
    use super::{Protocol, Statement, Witness};
    use crate::{
        commitments::Commitment,
        parameters::Parameters,
        protocols::{
            hash_to_prime::bp::Protocol as HPProtocol,
            membership::transcript::{TranscriptProverChannel, TranscriptVerifierChannel},
        },
    };
    use accumulator::group::Rsa2048;
    use accumulator::{group::Group, AccumulatorWithoutHashToPrime};
    use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
    use merlin::Transcript;
    use rand::thread_rng;
    use rug::rand::RandState;
    use rug::Integer;
    use std::cell::RefCell;

    const LARGE_PRIMES: [u64; 4] = [
        553_525_575_239_331_913,
        12_702_637_924_034_044_211,
        378_373_571_372_703_133,
        8_640_171_141_336_142_787,
    ];

    #[test]
    fn test_e2e_prime() {
        let params = Parameters::from_curve::<Scalar>().unwrap().0;
        let mut rng1 = RandState::new();
        rng1.seed(&Integer::from(13));
        let mut rng2 = thread_rng();

        let mut crs =
            crate::protocols::membership::Protocol::<Rsa2048, RistrettoPoint>::setup(
                &params, &mut rng1, &mut rng2,
            )
            .unwrap()
            .crs;
        let protocol = Protocol::<Rsa2048, RistrettoPoint>::from_crs(&crs);

        let value = Integer::from(Integer::u_pow_u(
            2,
            (crs.parameters.hash_to_prime_bits) as u32,
        )) - &Integer::from(129);
        let randomness = Integer::from(5);
        let commitment = protocol
            .crs
            .crs_modeq
            .pedersen_commitment_parameters
            .commit(&value, &randomness)
            .unwrap();

        let accum =
            accumulator::Accumulator::<Rsa2048, Integer, AccumulatorWithoutHashToPrime>::empty();
        let accum = accum.add(
            &LARGE_PRIMES
                .iter()
                .skip(1)
                .map(|p| Integer::from(*p))
                .collect::<Vec<_>>(),
        );

        let accum = accum.add_with_proof(&[value.clone()]);
        let acc = accum.0.value;
        let w = accum.1.witness.0.value;
        assert_eq!(Rsa2048::exp(&w, &value), acc);

        let proof_transcript = RefCell::new(Transcript::new(b"membership"));
        crs.crs_hash_to_prime.hash_to_prime_parameters.transcript = Some(proof_transcript.clone());
        let mut verifier_channel = TranscriptVerifierChannel::new(&crs, &proof_transcript);
        let statement = Statement {
            c_e_q: commitment,
            c_p: acc,
        };
        protocol
            .prove(
                &mut verifier_channel,
                &mut rng1,
                &mut rng2,
                &statement,
                &Witness {
                    e: value,
                    r_q: randomness,
                    w,
                },
            )
            .unwrap();
        let proof = verifier_channel.proof().unwrap();
        let verification_transcript = RefCell::new(Transcript::new(b"membership"));
        crs.crs_hash_to_prime.hash_to_prime_parameters.transcript =
            Some(verification_transcript.clone());
        let mut prover_channel =
            TranscriptProverChannel::new(&crs, &verification_transcript, &proof);
        protocol.verify(&mut prover_channel, &statement).unwrap();
    }
}
