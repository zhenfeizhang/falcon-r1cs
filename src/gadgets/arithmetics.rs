use super::*;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use num_bigint::BigUint;

/// Generate the variables c = a * B mod 12289;
/// with a guarantee that the inputs a and b satisfies:
/// * a is a dim n vector with a_i < 12289
/// * b is an n-by-m matrix with b_ij < 12289
/// Cost: (29 + a.len())*b.row() constraints
#[allow(dead_code)]
pub(crate) fn vector_matrix_mul_mod<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &[FpVar<F>],
    b: &[&[FpVar<F>]],
    modulus_var: &FpVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    if a.is_empty() || b.is_empty() {
        panic!("Invalid input length: a {} vs b {}", a.len(), b.len());
    }

    b.iter()
        .map(|&b_i| inner_product_mod(cs.clone(), a, b_i, modulus_var))
        .collect::<Result<Vec<_>, _>>()
}

/// Generate the variable c = <a \cdot b> mod 12289;
/// with a guarantee that the inputs a and b satisfies:
/// * a_i < 12289
/// * b_i < 12289
/// Cost: 29 + a.len() constraints
pub(crate) fn inner_product_mod<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &[FpVar<F>],
    b: &[FpVar<F>],
    modulus_var: &FpVar<F>,
) -> Result<FpVar<F>, SynthesisError> {
    if a.len() != b.len() || a.is_empty() {
        panic!("Invalid input length: a {} vs b {}", a.len(), b.len());
    }

    // we want to prove that `c = <a \cdot b> mod 12289`
    // that is
    // (1) a_0 * b_0 + a_1 * b_1 + ... + a_k * b_k - t * 12289 = c
    // for some unknown t, with
    // (2) c < 12289
    //
    // Note that this implementation assumes the
    // native field's order is greater than 12289^2
    // so we do not have any overflows
    //
    // also note that this method is slightly more efficient
    // than calling mul_mod iteratively

    // rebuild the field elements
    let a_val = a.value()?;
    let b_val = b.value()?;
    let mut ab_val = a_val[0] * b_val[0];
    for (&a_i, &b_i) in a_val.iter().zip(b_val.iter()).skip(1) {
        ab_val += a_i * b_i;
    }
    let ab_int: BigUint = ab_val.into();

    let modulus_int: BigUint = F::from(12289u64).into();
    let t_int = &ab_int / &modulus_int;
    let c_int = &ab_int % &modulus_int;

    let t_val = F::from(t_int);
    let c_val = F::from(c_int);

    // cast the variables
    let t_var = FpVar::<F>::new_witness(cs.clone(), || Ok(t_val))?;
    let c_var = FpVar::<F>::new_witness(cs.clone(), || Ok(c_val))?;

    // (1) a_0 * b_0 + a_1 * b_1 + ... + a_k * b_k - t * 12289 = c
    let mut ab_var = &a[0] * &b[0];
    for (a_i, b_i) in a.iter().zip(b.iter()).skip(1) {
        ab_var += a_i * b_i;
    }

    let t_12289 = t_var * modulus_var;
    let left = ab_var - t_12289;
    left.enforce_equal(&c_var)?;

    // (2) c < 12289
    enforce_less_than_12289(cs, &c_var)?;

    Ok(c_var)
}

/// Generate the variable c = a * b mod 12289;
/// with a guarantee that the inputs a and b satisfies:
/// * a < 12289
/// * b < 12289
/// Cost: 30 constraints
#[allow(dead_code)]
fn mul_mod<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &FpVar<F>,
    b: &FpVar<F>,
    modulus_var: &FpVar<F>,
) -> Result<FpVar<F>, SynthesisError> {
    // we want to prove that `c = a * b mod 12289`
    // that is
    // (1) a * b - t * 12289 = c
    // for some unknown t, with
    // (2) c < 12289
    //
    // Note that this implementation assumes the
    // native field's order is greater than 12289^2
    // so we do not have any overflows

    // rebuild the field elements
    let a_val = a.value()?;
    let b_val = b.value()?;
    let ab_val = a_val * b_val;
    let ab_int: BigUint = ab_val.into();

    let modulus_int: BigUint = F::from(12289u64).into();
    let t_int = &ab_int / &modulus_int;
    let c_int = &ab_int % &modulus_int;

    let t_val = F::from(t_int);
    let c_val = F::from(c_int);

    // cast the variables
    let t_var = FpVar::<F>::new_witness(cs.clone(), || Ok(t_val))?;
    let c_var = FpVar::<F>::new_witness(cs.clone(), || Ok(c_val))?;

    // (1) a * b - t * 12289 = c
    let ab_var = a * b;
    let t_12289 = t_var * modulus_var;
    let left = ab_var - t_12289;
    left.enforce_equal(&c_var)?;

    // (2) c < 12289
    enforce_less_than_12289(cs, &c_var)?;

    Ok(c_var)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ed_on_bls12_381::fq::Fq;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{rand::Rng, test_rng, UniformRand};

    macro_rules! test_mul_mod {
        ($a:expr, $b:expr, $c:expr, $satisfied:expr) => {
            let cs = ConstraintSystem::<Fq>::new_ref();
            let a = Fq::from($a);
            let b = Fq::from($b);
            let c = Fq::from($c);

            let a_var = FpVar::<Fq>::new_witness(cs.clone(), || Ok(a)).unwrap();
            let b_var = FpVar::<Fq>::new_witness(cs.clone(), || Ok(b)).unwrap();
            let const_12289_var =
                FpVar::<Fq>::new_constant(cs.clone(), Fq::from(12289u16)).unwrap();

            let num_instance_variables = cs.num_instance_variables();
            let num_witness_variables = cs.num_witness_variables();
            let num_constraints = cs.num_constraints();

            let c_var = mul_mod(cs.clone(), &a_var, &b_var, &const_12289_var).unwrap();
            println!(
                "number of variables {} {} and constraints {}\n",
                cs.num_instance_variables() - num_instance_variables,
                cs.num_witness_variables() - num_witness_variables,
                cs.num_constraints() - num_constraints,
            );

            let c_var2 = FpVar::<Fq>::new_witness(cs.clone(), || Ok(c)).unwrap();
            c_var.enforce_equal(&c_var2).unwrap();
            assert_eq!(cs.is_satisfied().unwrap(), $satisfied);

            assert_eq!(
                c_var.value().unwrap() == c,
                $satisfied,
                "c_var: {}\nc: {}",
                c_var.value().unwrap().into_repr(),
                c.into_repr()
            );
        };
    }

    #[test]
    fn test_mul_mod() {
        // =======================
        // good path
        // =======================
        // the meaning of life
        test_mul_mod!(6, 7, 42, true);

        // edge case: 0
        test_mul_mod!(0, 100, 0, true);
        test_mul_mod!(100, 0, 0, true);

        // edge case: wraparound
        test_mul_mod!(5, 12288, 12284, true);

        // =======================
        // bad path
        // =======================
        // wrong value
        test_mul_mod!(6, 7, 41, false);
        test_mul_mod!(5, 12288, 12283, false);

        // assert!(false)
    }

    fn inner_product(a: &[Fq], b: &[Fq]) -> Fq {
        let mut res = a[0] * b[0];
        for (&a_i, &b_i) in a.iter().zip(b.iter()).skip(1) {
            res += a_i * b_i;
        }
        let res_uint: BigUint = res.into();
        let res_uint = res_uint % BigUint::from(12289u64);
        Fq::from(res_uint)
    }

    #[test]
    fn test_inner_product_mod() {
        let mut rng = test_rng();
        for i in 1..10 {
            let dim = 1 << i;
            let cs = ConstraintSystem::<Fq>::new_ref();
            let a = (0..dim)
                .map(|_| Fq::from(rng.gen_range(0..12289)))
                .collect::<Vec<Fq>>();
            let b = (0..dim)
                .map(|_| Fq::from(rng.gen_range(0..12289)))
                .collect::<Vec<Fq>>();
            let c = inner_product(&a, &b);

            let a_var: Vec<FpVar<Fq>> = a
                .iter()
                .map(|x| FpVar::<Fq>::new_witness(cs.clone(), || Ok(x)).unwrap())
                .collect();
            let b_var: Vec<FpVar<Fq>> = b
                .iter()
                .map(|x| FpVar::<Fq>::new_witness(cs.clone(), || Ok(x)).unwrap())
                .collect();
            let const_12289_var =
                FpVar::<Fq>::new_constant(cs.clone(), Fq::from(12289u16)).unwrap();

            let num_instance_variables = cs.num_instance_variables();
            let num_witness_variables = cs.num_witness_variables();
            let num_constraints = cs.num_constraints();

            let c_var =
                inner_product_mod(cs.clone(), a_var.as_ref(), b_var.as_ref(), &const_12289_var)
                    .unwrap();
            println!(
                "number of variables {} {} and constraints {}\n",
                cs.num_instance_variables() - num_instance_variables,
                cs.num_witness_variables() - num_witness_variables,
                cs.num_constraints() - num_constraints,
            );

            let c_var2 = FpVar::<Fq>::new_witness(cs.clone(), || Ok(c)).unwrap();
            c_var.enforce_equal(&c_var2).unwrap();
            assert!(cs.is_satisfied().unwrap());
            assert_eq!(c_var.value().unwrap(), c,);

            let bad_c_var =
                FpVar::<Fq>::new_witness(cs.clone(), || Ok(Fq::rand(&mut rng))).unwrap();
            c_var.enforce_equal(&bad_c_var).unwrap();
            assert!(!cs.is_satisfied().unwrap());
        }

        // assert!(false)
    }

    #[test]
    fn test_vector_matrix_mod() {
        let mut rng = test_rng();
        for i in 1..10 {
            let row = 1 << i;
            let cs = ConstraintSystem::<Fq>::new_ref();
            let a = (0..row)
                .map(|_| Fq::from(rng.gen_range(0..12289)))
                .collect::<Vec<Fq>>();

            for j in 1..10 {
                let col = 1 << j;

                let b: Vec<Vec<Fq>> = (0..col)
                    .map(|_| {
                        (0..row)
                            .map(|_| Fq::from(rng.gen_range(0..12289)))
                            .collect::<Vec<Fq>>()
                    })
                    .collect();

                let c: Vec<Fq> = b.iter().map(|b_i| inner_product(&a, b_i)).collect();

                let a_var: Vec<FpVar<Fq>> = a
                    .iter()
                    .map(|x| FpVar::<Fq>::new_witness(cs.clone(), || Ok(x)).unwrap())
                    .collect();
                let b_var: Vec<Vec<FpVar<Fq>>> = b
                    .iter()
                    .map(|bi| {
                        bi.iter()
                            .map(|bij| FpVar::<Fq>::new_witness(cs.clone(), || Ok(bij)).unwrap())
                            .collect::<Vec<FpVar<Fq>>>()
                    })
                    .collect();
                let const_12289_var =
                    FpVar::<Fq>::new_constant(cs.clone(), Fq::from(12289u16)).unwrap();

                let b_var_ref: Vec<&[FpVar<Fq>]> = b_var.iter().map(|x| x.as_ref()).collect();

                let num_instance_variables = cs.num_instance_variables();
                let num_witness_variables = cs.num_witness_variables();
                let num_constraints = cs.num_constraints();

                let c_var = vector_matrix_mul_mod(
                    cs.clone(),
                    a_var.as_ref(),
                    b_var_ref.as_ref(),
                    &const_12289_var,
                )
                .unwrap();
                println!(
                    "number of variables {} {} and constraints {}\n",
                    cs.num_instance_variables() - num_instance_variables,
                    cs.num_witness_variables() - num_witness_variables,
                    cs.num_constraints() - num_constraints,
                );

                let c_var2: Vec<FpVar<Fq>> = c
                    .iter()
                    .map(|x| FpVar::<Fq>::new_witness(cs.clone(), || Ok(x)).unwrap())
                    .collect();
                c_var.enforce_equal(&c_var2).unwrap();
                assert!(cs.is_satisfied().unwrap());
                assert_eq!(c_var.value().unwrap(), c);
            }
        }

        // assert!(false)
    }
}
