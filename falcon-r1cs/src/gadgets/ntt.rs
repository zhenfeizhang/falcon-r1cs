#![allow(clippy::many_single_char_names)]

use super::*;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use falcon_rust::{N, NTT_TABLE};

/// The circuit to convert a poly into its NTT form
/// Cost 15360 constraints.
/// Inputs:
/// - cs: constraint system
/// - input: the wires of the input polynomial
/// - const_vars: the [q, 2*q^2, 4 * q^3, ..., 2^9 * q^10] constant wires
/// - param: the forward NTT table in wire format
pub fn ntt_circuit<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    input: &[FpVar<F>],
    const_vars: &[FpVar<F>],
    param: &[FpVar<F>],
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    if input.len() != N {
        panic!("input length {} is not N", input.len())
    }
    let mut output = input.to_vec();

    let mut t = N;
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
                // for the l-th loop, we know that all the output's
                // coefficients are less than q^{l+1}
                // therefore we have
                //  u < 2^l * q^{l+1}
                //  v < 2^l * q^{l+2}
                // and we have
                //  neg_v = q^{l+2} - v
                // note that this works when q^10 < F::Modulus
                // so all operations here becomes native field operations
                let u = output[j].clone();
                let v = &output[j + ht] * &s;
                let neg_v = &const_vars[l + 1] - &v;

                // output[j] and output[j+ht]
                // are between 0 and 2^{l+1} * q^{l+2}
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
    // this is the only place that we need non-native circuits
    for e in output.iter_mut() {
        *e = mod_q(cs.clone(), e, &const_vars[0])?;
    }

    Ok(output)
}

pub fn ntt_param_var<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let mut res = Vec::new();

    for e in NTT_TABLE[0..N].as_ref() {
        res.push(FpVar::<F>::new_constant(cs.clone(), F::from(*e))?)
    }

    Ok(res)
}

#[allow(dead_code)]
pub(crate) fn inv_ntt_param_var<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let mut res = Vec::new();

    for e in NTT_TABLE[0..N].as_ref() {
        res.push(FpVar::<F>::new_constant(cs.clone(), F::from(*e))?)
    }

    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ed_on_bls12_381::fq::Fq;
    use ark_ff::Field;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{rand::Rng, test_rng};
    use falcon_rust::{ntt, MODULUS};

    #[test]
    fn test_ntt_mul_circuit() {
        let mut rng = test_rng();

        for _ in 0..10 {
            let cs = ConstraintSystem::<Fq>::new_ref();
            let param_vars = ntt_param_var(cs.clone()).unwrap();
            // the [q, 2*q^2, 4 * q^3, ..., 2^9 * q^10] constant wires
            let const_power_q_vars: Vec<FpVar<Fq>> = (1..11)
                .map(|x| {
                    FpVar::<Fq>::new_constant(
                        cs.clone(),
                        Fq::from(1 << (x - 1)) * Fq::from(MODULUS).pow(&[x]),
                    )
                    .unwrap()
                })
                .collect();
            let poly_u32 = (0..N)
                .map(|_| rng.gen_range(0..12289))
                .collect::<Vec<u32>>();
            let poly = poly_u32.iter().map(|x| Fq::from(*x)).collect::<Vec<Fq>>();
            let poly_var: Vec<FpVar<Fq>> = poly
                .iter()
                .map(|x| FpVar::<Fq>::new_witness(cs.clone(), || Ok(*x)).unwrap())
                .collect();

            let output = ntt(poly_u32.as_ref());

            let num_instance_variables = cs.num_instance_variables();
            let num_witness_variables = cs.num_witness_variables();
            let num_constraints = cs.num_constraints();

            let output_var =
                ntt_circuit(cs.clone(), &poly_var, &const_power_q_vars, &param_vars).unwrap();
            println!(
                "number of variables {} {} and constraints {}\n",
                cs.num_instance_variables() - num_instance_variables,
                cs.num_witness_variables() - num_witness_variables,
                cs.num_constraints() - num_constraints,
            );

            for i in 0..N {
                assert_eq!(Fq::from(output[i]), output_var[i].value().unwrap())
            }
        }

        // assert!(false)
    }
}
