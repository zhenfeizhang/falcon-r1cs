use crate::mod_q;
use ark_ff::PrimeField;
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, Result as ArkResult, SynthesisError};
use falcon_rust::{NTTPolynomial, Polynomial};
use std::ops::{Add, Mul};

#[derive(Debug, Clone)]
pub struct NTTPolyVar<F: PrimeField>(pub(crate) Vec<FpVar<F>>);

#[derive(Debug, Clone)]
pub struct PolyVar<F: PrimeField>(pub(crate) Vec<FpVar<F>>);

impl<F: PrimeField> Add for NTTPolyVar<F> {
    type Output = Self;

    /// generate the variables for a + b without mod reduction
    fn add(self, other: Self) -> <Self as Add<Self>>::Output {
        let mut res = Vec::new();
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            res.push(a.clone() + b.clone())
        }
        Self(res)
    }
}

impl<F: PrimeField> Mul for NTTPolyVar<F> {
    type Output = Self;

    /// generate the variables for a * b without mod reduction
    fn mul(self, other: Self) -> <Self as Mul<Self>>::Output {
        let mut res = Vec::new();
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            res.push(a.clone() * b.clone())
        }
        Self(res)
    }
}

impl<F: PrimeField> NTTPolyVar<F> {
    // allocate variables for a give ntt_polynomial
    pub fn alloc_vars(
        cs: impl Into<Namespace<F>>,
        poly: &NTTPolynomial,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let mut vec = Vec::new();
        for &value in poly.coeff().iter() {
            vec.push(FpVar::new_variable(
                cs.clone(),
                || Ok(F::from(value)),
                mode,
            )?);
        }
        Ok(Self(vec))
    }

    /// generate constraints proving that c = a * b without mod reduction
    pub fn enforce_product(a: &Self, b: &Self, c: &Self) -> ArkResult<()> {
        for (ai, (bi, ci)) in a.0.iter().zip(b.0.iter().zip(c.0.iter())) {
            let tmp = ai * bi;
            tmp.enforce_equal(ci)?;
        }
        Ok(())
    }

    /// generate constraints proving that c = a + b without mod reduction
    pub fn enforce_sum(a: &Self, b: &Self, c: &Self) -> ArkResult<()> {
        for (ai, (bi, ci)) in a.0.iter().zip(b.0.iter().zip(c.0.iter())) {
            let tmp = ai + bi;
            tmp.enforce_equal(ci)?;
        }
        Ok(())
    }

    pub fn mod_q(&self, cs: ConstraintSystemRef<F>, modulus_var: &FpVar<F>) -> Self {
        let res: Vec<FpVar<F>> = self
            .0
            .iter()
            .map(|x| mod_q(cs.clone(), x, modulus_var).unwrap())
            .collect();
        Self(res)
    }

    /// Access the coefficients
    pub fn coeff(&self) -> &[FpVar<F>] {
        &self.0
    }
}

impl<F: PrimeField> Add for PolyVar<F> {
    type Output = Self;

    /// generate the variables for a + b without mod reduction
    fn add(self, other: Self) -> <Self as Add<Self>>::Output {
        let mut res = Vec::new();
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            res.push(a.clone() + b.clone())
        }
        Self(res)
    }
}

impl<F: PrimeField> Mul for PolyVar<F> {
    type Output = Self;

    /// generate the variables for a * b without mod reduction
    fn mul(self, other: Self) -> <Self as Mul<Self>>::Output {
        let mut res = Vec::new();
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            res.push(a.clone() * b.clone())
        }
        Self(res)
    }
}

impl<F: PrimeField> PolyVar<F> {
    // allocate variables for a give ntt_polynomial
    pub fn alloc_vars(
        cs: impl Into<Namespace<F>>,
        poly: &Polynomial,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let mut vec = Vec::new();
        for &value in poly.coeff().iter() {
            vec.push(FpVar::new_variable(
                cs.clone(),
                || Ok(F::from(value)),
                mode,
            )?);
        }
        Ok(Self(vec))
    }

    /// generate constraints proving that c = a * b without mod reduction
    pub fn enforce_product(a: &Self, b: &Self, c: &Self) -> ArkResult<()> {
        for (ai, (bi, ci)) in a.0.iter().zip(b.0.iter().zip(c.0.iter())) {
            let tmp = ai * bi;
            tmp.enforce_equal(ci)?;
        }
        Ok(())
    }

    /// generate constraints proving that c = a + b without mod reduction
    pub fn enforce_sum(a: &Self, b: &Self, c: &Self) -> ArkResult<()> {
        for (ai, (bi, ci)) in a.0.iter().zip(b.0.iter().zip(c.0.iter())) {
            let tmp = ai + bi;
            tmp.enforce_equal(ci)?;
        }
        Ok(())
    }

    /// Access the coefficients
    pub fn coeff(&self) -> &[FpVar<F>] {
        &self.0
    }
}

// TODO: more tests for the functions
