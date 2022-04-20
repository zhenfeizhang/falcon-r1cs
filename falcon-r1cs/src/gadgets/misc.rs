use super::*;
use ark_ff::PrimeField;
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

/// Constraint that a = bits[0] + 2 bits[1] + 2^2 bits[2] ...
pub(crate) fn enforce_decompose<F: PrimeField>(
    a: &FpVar<F>,
    bits: &[Boolean<F>],
) -> Result<(), SynthesisError> {
    if bits.is_empty() {
        panic!("Invalid input length: {}", bits.len());
    }

    let mut res: FpVar<F> = bits[bits.len() - 1].clone().into();
    for e in bits.iter().rev().skip(1) {
        res = res.double()? + FpVar::<F>::from(e.clone());
    }

    res.enforce_equal(a)?;
    Ok(())
}

// compute the l2 norm of vector a where a's coefficients
// are positive between [0, 12289).
// We need to firstly lift it to [-6144, 6144) and then
// compute the norm.
pub fn l2_norm_var<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    input: &[FpVar<F>],
    modulus_var: &FpVar<F>,
) -> Result<FpVar<F>, SynthesisError> {
    let mut res = FpVar::<F>::conditionally_select(
        &is_less_than_6144(cs.clone(), &input[0])?,
        &input[0],
        &(modulus_var - &input[0]),
    )?;
    res = &res * &res;
    for e in input.iter().skip(1) {
        let tmp = FpVar::<F>::conditionally_select(
            &is_less_than_6144(cs.clone(), e)?,
            e,
            &(modulus_var - e),
        )?;
        res += &tmp * &tmp
    }

    Ok(res)
}
