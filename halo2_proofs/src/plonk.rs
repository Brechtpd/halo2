//! This module provides an implementation of a variant of (Turbo)[PLONK][plonk]
//! that is designed specifically for the polynomial commitment scheme described
//! in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021
//! [plonk]: https://eprint.iacr.org/2019/953

use blake2b_simd::Params as Blake2bParams;
use group::ff::Field;

use ark_std::perf_trace::{AtomicUsize, Ordering};
use crate::arithmetic::{CurveAffine, FieldExt};
use crate::helpers::CurveRead;
use crate::poly::{
    commitment::Params, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff,
    PinnedEvaluationDomain, Polynomial,
};
use crate::transcript::{ChallengeScalar, EncodedChallenge, Transcript};

mod assigned;
mod circuit;
mod error;
mod evaluation;
mod keygen;
mod lookup;
pub(crate) mod permutation;
mod vanishing;

mod prover;
mod verifier;

pub use assigned::*;
pub use circuit::*;
pub use error::*;
pub use keygen::*;
pub use prover::*;
pub use verifier::*;

use evaluation::Evaluator;
use std::env::var;
use std::io;
use std::time::Instant;


/// Temp
#[allow(missing_debug_implementations)]
pub struct MeasurementInfo {
    /// Temp
    pub measure: bool,
    /// Temp
    pub time: /*TimerInfo*/Instant,
    /// Message
    pub message: String,
    /// Indent
    pub indent: usize,
}

/// TEMP
pub static NUM_INDENT: AtomicUsize = AtomicUsize::new(0);

/// Temp
pub fn get_time() -> Instant {
    Instant::now()
}

/// Temp
pub fn get_duration(start: Instant) -> usize {
    let final_time = Instant::now() - start;
    let secs = final_time.as_secs() as usize;
    let millis = final_time.subsec_millis() as usize;
    let micros = (final_time.subsec_micros() % 1000) as usize;
    secs * 1000000 + millis * 1000 + micros
}

/// Temp
pub fn log_measurement(indent: Option<usize>, msg: String, duration: usize) {
    let indent = indent.unwrap_or(0);
    println!("{}{} ........ {}s", "*".repeat(indent), msg, (duration as f32)/1000000.0);
}

/// Temp
pub fn start_measure(msg: String, always: bool) -> MeasurementInfo {
    let measure: u32 = var("MEASURE")
    .unwrap_or_else(|_| "0".to_string())
    .parse()
    .expect("Cannot parse MEASURE env var as u32");

    let indent = NUM_INDENT.fetch_add(1, Ordering::Relaxed);

    if always || measure == 1/* || msg.starts_with("compressed_cosets")*/ {
        MeasurementInfo {
            measure: true,
            time: get_time(),
            message: msg,
            indent,
        }
    } else {
        MeasurementInfo {
            measure: false,
            time: get_time(),
            message: "".to_string(),
            indent,
        }
    }
}

/// Temp
pub fn stop_measure(info: MeasurementInfo) -> usize {
    NUM_INDENT.fetch_sub(1, Ordering::Relaxed);
    let duration = get_duration(info.time);
    if info.measure {
        log_measurement(Some(info.indent), info.message, duration);
    }
    duration
}

/// Get env variable
pub fn env_value(key: &str, default: usize) -> usize {
    match var(key) {
        Ok(val) => val.parse().unwrap(),
        Err(_) => default,
    }
}

/// Temp
pub fn log_info(msg: String) {
    if env_value("INFO", 0) != 0 {
        println!("{}", msg);
    }
}

/// This is a verifying key which allows for the verification of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct VerifyingKey<C: CurveAffine> {
    domain: EvaluationDomain<C::Scalar>,
    fixed_commitments: Vec<C>,
    permutation: permutation::VerifyingKey<C>,
    cs: ConstraintSystem<C::Scalar>,
    /// Cached maximum degree of `cs` (which doesn't change after construction).
    cs_degree: usize,
    /// The representative of this `VerifyingKey` in transcripts.
    transcript_repr: C::Scalar,
}

impl<C: CurveAffine> VerifyingKey<C> {
    fn from_parts(
        domain: EvaluationDomain<C::Scalar>,
        fixed_commitments: Vec<C>,
        permutation: permutation::VerifyingKey<C>,
        cs: ConstraintSystem<C::Scalar>,
    ) -> Self {
        // Compute cached values.
        let cs_degree = cs.degree();

        let mut vk = Self {
            domain,
            fixed_commitments,
            permutation,
            cs,
            cs_degree,
            // Temporary, this is not pinned.
            transcript_repr: C::Scalar::zero(),
        };

        let mut hasher = Blake2bParams::new()
            .hash_length(64)
            .personal(b"Halo2-Verify-Key")
            .to_state();

        let s = format!("{:?}", vk.pinned());

        hasher.update(&(s.len() as u64).to_le_bytes());
        hasher.update(s.as_bytes());

        // Hash in final Blake2bState
        vk.transcript_repr = C::Scalar::from_bytes_wide(hasher.finalize().as_array());

        vk
    }

    /// Hashes a verification key into a transcript.
    pub fn hash_into<E: EncodedChallenge<C>, T: Transcript<C, E>>(
        &self,
        transcript: &mut T,
    ) -> io::Result<()> {
        transcript.common_scalar(self.transcript_repr)?;

        Ok(())
    }

    /// Obtains a pinned representation of this verification key that contains
    /// the minimal information necessary to reconstruct the verification key.
    pub fn pinned(&self) -> PinnedVerificationKey<'_, C> {
        PinnedVerificationKey {
            base_modulus: C::Base::MODULUS,
            scalar_modulus: C::Scalar::MODULUS,
            domain: self.domain.pinned(),
            fixed_commitments: &self.fixed_commitments,
            permutation: &self.permutation,
            cs: self.cs.pinned(),
        }
    }

    /// Returns commitments of fixed polynomials
    pub fn fixed_commitments(&self) -> &Vec<C> {
        &self.fixed_commitments
    }

    /// Returns `VerifyingKey` of permutation
    pub fn permutation(&self) -> &permutation::VerifyingKey<C> {
        &self.permutation
    }

    /// Returns `ConstraintSystem`
    pub fn cs(&self) -> &ConstraintSystem<C::Scalar> {
        &self.cs
    }
}

/// Minimal representation of a verification key that can be used to identify
/// its active contents.
#[allow(dead_code)]
#[derive(Debug)]
pub struct PinnedVerificationKey<'a, C: CurveAffine> {
    base_modulus: &'static str,
    scalar_modulus: &'static str,
    domain: PinnedEvaluationDomain<'a, C::Scalar>,
    cs: PinnedConstraintSystem<'a, C::Scalar>,
    fixed_commitments: &'a Vec<C>,
    permutation: &'a permutation::VerifyingKey<C>,
}
/// This is a proving key which allows for the creation of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct ProvingKey<C: CurveAffine> {
    vk: VerifyingKey<C>,
    l0: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    l_last: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    l_active_row: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    fixed_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
    fixed_polys: Vec<Polynomial<C::Scalar, Coeff>>,
    fixed_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    permutation: permutation::ProvingKey<C>,
    ev: Evaluator<C>,
}

impl<C: CurveAffine> ProvingKey<C> {
    /// Get the underlying [`VerifyingKey`].
    pub fn get_vk(&self) -> &VerifyingKey<C> {
        &self.vk
    }
}

impl<C: CurveAffine> VerifyingKey<C> {
    /// Get the underlying [`EvaluationDomain`].
    pub fn get_domain(&self) -> &EvaluationDomain<C::Scalar> {
        &self.domain
    }
}

#[derive(Clone, Copy, Debug)]
struct Theta;
type ChallengeTheta<F> = ChallengeScalar<F, Theta>;

#[derive(Clone, Copy, Debug)]
struct Beta;
type ChallengeBeta<F> = ChallengeScalar<F, Beta>;

#[derive(Clone, Copy, Debug)]
struct Gamma;
type ChallengeGamma<F> = ChallengeScalar<F, Gamma>;

#[derive(Clone, Copy, Debug)]
struct Y;
type ChallengeY<F> = ChallengeScalar<F, Y>;

#[derive(Clone, Copy, Debug)]
struct X;
type ChallengeX<F> = ChallengeScalar<F, X>;
