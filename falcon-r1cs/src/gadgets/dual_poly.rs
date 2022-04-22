use crate::{NTTPolyVar, PolyVar};
use ark_ff::PrimeField;
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use falcon_rust::DualPolynomial;

#[derive(Debug, Clone)]
pub struct DualPolyVar<F: PrimeField> {
    pub pos: PolyVar<F>,
    pub neg: PolyVar<F>,
}

impl<F: PrimeField> DualPolyVar<F> {
    // allocate variables for a give ntt_polynomial
    pub fn alloc_vars(
        cs: impl Into<Namespace<F>> + Clone,
        dual_poly: &DualPolynomial,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            pos: PolyVar::<F>::alloc_vars(cs.clone(), &dual_poly.pos, mode)?,
            neg: PolyVar::<F>::alloc_vars(cs.clone(), &dual_poly.neg, mode)?,
        })
    }
}

#[derive(Debug, Clone)]
pub struct DualNTTPolyVar<F: PrimeField> {
    pub pos: NTTPolyVar<F>,
    pub neg: NTTPolyVar<F>,
}

impl<F: PrimeField> DualNTTPolyVar<F> {
    pub fn ntt_circuit(
        cs: ConstraintSystemRef<F>,
        input: &DualPolyVar<F>,
        const_vars: &[FpVar<F>],
        param: &[FpVar<F>],
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            pos: NTTPolyVar::ntt_circuit(cs.clone(), &input.pos, const_vars, param)?,
            neg: NTTPolyVar::ntt_circuit(cs.clone(), &input.neg, const_vars, param)?,
        })
    }
}
