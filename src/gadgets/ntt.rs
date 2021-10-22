#![allow(clippy::many_single_char_names)]

use super::*;
use crate::gadgets::arithmetics::mul_mod;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use falcon_rust::NTT_TABLE;

/// The circuit to convert a poly into its NTT form
/// Cost 84480 constraints.
pub fn ntt_circuit<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    input: &[FpVar<F>],
    const_var: &FpVar<F>,
    param: &[FpVar<F>],
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    if input.len() != 512 {
        panic!("input length {} is not 512", input.len())
    }
    let mut output = input.to_vec();

    let n = 512;
    let mut t = n;
    for l in 0..9 {
        let m = 1 << l;
        let ht = t / 2;
        let mut i = 0;
        let mut j1 = 0;
        while i < m {
            let s = param[m + i].clone();
            let j2 = j1 + ht;
            let mut j = j1;
            while j < j2 {
                let u = output[j].clone();
                // here both v and neg_v are less than 12289
                // we therefore need a mul_mod algorithm
                let v = mul_mod(cs.clone(), &output[j + ht], &s, const_var)?;
                let neg_v = const_var - &v;

                // output[j] and output[j+ht]
                // are between 0 and 12289*2
                output[j] = &u + &v;
                output[j + ht] = &u + &neg_v;
                j += 1;
            }
            i += 1;
            j1 += t
        }
        t = ht;
    }

    // perform a final mod reduction to make the
    // output into the right range
    for e in output.iter_mut() {
        *e = mod_q(cs.clone(), e, const_var)?;
    }

    Ok(output)
}

pub fn ntt_param_var<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let mut res = Vec::new();

    for e in NTT_TABLE[0..512].as_ref() {
        res.push(FpVar::<F>::new_constant(cs.clone(), F::from(*e))?)
    }

    Ok(res)
}

#[allow(dead_code)]
pub(crate) fn inv_ntt_param_var<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let mut res = Vec::new();

    for e in NTT_TABLE[0..512].as_ref() {
        res.push(FpVar::<F>::new_constant(cs.clone(), F::from(*e))?)
    }

    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ed_on_bls12_381::fq::Fq;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{rand::Rng, test_rng};
    use falcon_rust::ntt;

    #[test]
    fn test_ntt_mul_circuit() {
        let mut rng = test_rng();

        for _ in 0..10 {
            let cs = ConstraintSystem::<Fq>::new_ref();
            let param_var = ntt_param_var(cs.clone()).unwrap();
            let poly_u32 = (0..512)
                .map(|_| rng.gen_range(0..12289))
                .collect::<Vec<u32>>();
            let poly = poly_u32.iter().map(|x| Fq::from(*x)).collect::<Vec<Fq>>();
            let poly_var: Vec<FpVar<Fq>> = poly
                .iter()
                .map(|x| FpVar::<Fq>::new_witness(cs.clone(), || Ok(*x)).unwrap())
                .collect();

            let const_12289_var =
                FpVar::<Fq>::new_constant(cs.clone(), Fq::from(12289u16)).unwrap();
            let output = ntt(poly_u32.as_ref());

            let num_instance_variables = cs.num_instance_variables();
            let num_witness_variables = cs.num_witness_variables();
            let num_constraints = cs.num_constraints();

            let output_var =
                ntt_circuit(cs.clone(), &poly_var, &const_12289_var, &param_var).unwrap();
            println!(
                "number of variables {} {} and constraints {}\n",
                cs.num_instance_variables() - num_instance_variables,
                cs.num_witness_variables() - num_witness_variables,
                cs.num_constraints() - num_constraints,
            );

            for i in 0..512 {
                assert_eq!(Fq::from(output[i]), output_var[i].value().unwrap())
            }
        }

        // assert!(false)
    }
}
