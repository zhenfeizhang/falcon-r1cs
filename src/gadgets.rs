use ark_ff::{BigInteger, PrimeField};
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

/// Constraint that the witness of a is smaller than 12289
/// Cost: 28 constraints.
/// (This improves the range proof of 1264 constraints as in Arkworks.)
pub(crate) fn enforce_less_than_12289<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &FpVar<F>,
) -> Result<(), SynthesisError> {
    let a_val = a.value()?;

    // suppressing this check so that unit test can test
    // bad paths
    #[cfg(not(test))]
    if a_val >= F::from(12289u64) {
        panic!("Invalid input: {}", a_val);
    }

    let a_bits = a_val.into_repr().to_bits_le();
    // a_bit_vars is the least 14 bits of a
    // (we only care for the first 14 bits of a_bits)
    let a_bit_vars = a_bits
        .iter()
        .take(14)
        .map(|x| Boolean::new_witness(cs.clone(), || Ok(x)))
        .collect::<Result<Vec<_>, _>>()?;

    // ensure that a_bits are the bit decomposition of a
    enforce_decompose(a, a_bit_vars.as_ref())?;

    // argue that a < 12289 = 2^13 + 2^12 + 1 via enforcing one of the following
    // - either a[13] == 0, or
    // - a[13] == 1 and
    //      - either a[12] == 0
    //      - or a[12] == 1 and a[11] && a[10] && ... && a[0] == 0

    // a[13] == 0
    (a_bit_vars[13].is_eq(&Boolean::FALSE)?)
        .or(
            // a[12] == 0
            &a_bit_vars[12].is_eq(&Boolean::FALSE)?.or(
                // a[11] && ... && a[0] == 0
                &Boolean::kary_or(a_bit_vars[0..12].as_ref())?.is_eq(&Boolean::FALSE)?,
            )?,
        )?
        .enforce_equal(&Boolean::TRUE)?;

    Ok(())
}

/// Constraint that the witness of a is smaller than 34034726
/// Cost: 47 constraints.
/// (This improves the range proof of 1264 constraints as in Arkworks.)
pub(crate) fn enforce_less_than_norm_bound<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &FpVar<F>,
) -> Result<(), SynthesisError> {
    // the norm bound is 0b10000001110101010000100110 which is 26 bits, i.e.,
    // 2^25 + 2^18 + 2^17 + 2^16 + 2^14 + 2^ 12 + 2^10 + 2^5 + 2^2 + 2

    let a_val = a.value()?;

    // suppressing this check so that unit test can test
    // bad paths
    #[cfg(not(test))]
    if a_val >= F::from(34034726u64) {
        panic!("Invalid input: {}", a_val);
    }

    let a_bits = a_val.into_repr().to_bits_le();
    // a_bit_vars is the least 26 bits of a
    // (we only care for the first 26 bits of a_bits)
    let a_bit_vars = a_bits
        .iter()
        .take(26)
        .map(|x| Boolean::new_witness(cs.clone(), || Ok(x)))
        .collect::<Result<Vec<_>, _>>()?;

    // ensure that a_bits are the bit decomposition of a
    enforce_decompose(a, a_bit_vars.as_ref())?;

    // argue that a < 0b10000001110101010000100110  via the following:
    // - a[25] == 0 or
    // - a[25] == 1 and a[19..24] == 0 and
    //    - either one of a[16..18] == 0
    //    - or a[16..18] == 1 and a[15] == 0 and
    //      - either a[14] == 0
    //      - or a[14] == 1 and a[13] == 0 and
    //          - either a[12] == 0
    //          - or a[12] == 1 and a[11] == 0 and
    //              - either a[10] == 0
    //              - or a[10] == 1 and a[6-9] == 0 and
    //                  - either a[5] == 0
    //                  - or a[5] == 1 and a[3] = a [4] == 0 and
    //                      - one of a[1] or a[2] == 0

    #[rustfmt::skip]
    // a[25] == 0
    (a_bit_vars[25].is_eq(&Boolean::FALSE)?).or(
        // a[25] == 1 and a[19..24] == 0 and
        &Boolean::kary_or(a_bit_vars[19..25].as_ref())?.is_eq(&Boolean::FALSE)?.and(
            // - either one of a[16..18] == 0
            &Boolean::kary_and(a_bit_vars[16..19].as_ref())?.is_eq(&Boolean::FALSE)?.or(
                // - or a[16..18] == 1 and a[15] == 0 and
                &a_bit_vars[15].is_eq(&Boolean::FALSE)?.and(
                    // - either a[14] == 0
                        &a_bit_vars[14].is_eq(&Boolean::FALSE)?.or(
                        // - or a[14] == 1 and a[13] == 0 and
                            &a_bit_vars[13].is_eq(&Boolean::FALSE)?.and(
                            // - either a[12] == 0
                                &a_bit_vars[12].is_eq(&Boolean::FALSE)?.or(
                                // - or a[12] == 1 and a[11] == 0 and   
                                    &a_bit_vars[11].is_eq(&Boolean::FALSE)?.and(
                                        // - either a[10] == 0
                                        &a_bit_vars[10].is_eq(&Boolean::FALSE)?.or(
                                            // - or a[10] == 1 and a[6-9] == 0 and
                                            &Boolean::kary_or(a_bit_vars[6..10].as_ref())?.is_eq(&Boolean::FALSE)?.and(
                                                // either a[5] == 0
                                                &a_bit_vars[5].is_eq(&Boolean::FALSE)?.or(
                                                    // - or a[5] == 1 and a[3] = a [4] == 0 and
                                                    &Boolean::kary_or(a_bit_vars[3..5].as_ref())?.is_eq(&Boolean::FALSE)?.and(
                                                        // - one of a[1] or a[2] == 0
                                                        &Boolean::kary_and(a_bit_vars[1..3].as_ref())?.is_eq(&Boolean::FALSE)?
                                                    )?
                                                )?
                                            )?
                                        )?
                                    )?
                                )?
                            )?
                        )?
                    )? 
                )?,
            )?,
        )?.enforce_equal(&Boolean::TRUE)?;

    Ok(())
}

/// Return a variable indicating if the input is less than 6144 or not
/// Cost: 18 constraints.
/// (This improves the range proof of 1264 constraints as in Arkworks.)
pub(crate) fn is_less_than_6144<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &FpVar<F>,
) -> Result<Boolean<F>, SynthesisError> {
    let a_val = a.value()?;

    // suppressing this check so that unit test can test
    // bad paths
    #[cfg(not(test))]
    if a_val >= F::from(6144u64) {
        panic!("Invalid input: {}", a_val);
    }

    let a_bits = a_val.into_repr().to_bits_le();
    // a_bit_vars is the least 14 bits of a
    // (we only care for the first 14 bits of a_bits)
    let a_bit_vars = a_bits
        .iter()
        .take(14)
        .map(|x| Boolean::new_witness(cs.clone(), || Ok(x)))
        .collect::<Result<Vec<_>, _>>()?;

    // ensure that a_bits are the bit decomposition of a
    enforce_decompose(a, a_bit_vars.as_ref())?;

    // argue that a < 6144 = 2^12 + 2^11 via the following:
    // - a[13] == 0 and
    // - either a[12] == 0 or a[11] == 0

    // a[13] == 0
    (a_bit_vars[13].is_eq(&Boolean::FALSE)?)
        // a[12] == 0
        .and(&a_bit_vars[12].is_eq(&Boolean::FALSE)?
            // a[11] == 0
        .   or(&a_bit_vars[11].is_eq(&Boolean::FALSE)?
            )?
        )?
        .is_eq(&Boolean::TRUE)
}

/// Constraint that a = bits[0] + 2 bits[1] + 2^2 bits[2] ...
fn enforce_decompose<F: PrimeField>(
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
pub(crate) fn l2_norm_var<F: PrimeField>(
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

// Turns out the following gadget is more costly than
// simply use `is_eq()`, LOL.
//
// /// Generate the variable fpr a ?= b;
// /// with a guarantee that the inputs a and b satisfies:
// /// * a < 12289 * 2
// /// * b < 12289 * 2
// /// Cost: TBD constraints
// pub(crate) fn is_equal<F: PrimeField>(
//     cs: ConstraintSystemRef<F>,
//     a: &FpVar<F>,
//     b: &FpVar<F>,
// ) -> Result<Boolean<F>, SynthesisError> {
//     let a_val = a.value()?;
//     let b_val = b.value()?;
//     let a_bits = a_val.into_repr().to_bits_le();
//     let b_bits = b_val.into_repr().to_bits_le();
//     // a_bit_vars is the least 15 bits of a
//     // (we only care for the first 15 bits of a_bits)
//     let a_bit_vars = a_bits
//         .iter()
//         .take(15)
//         .map(|x| Boolean::new_witness(cs.clone(), || Ok(x)))
//         .collect::<Result<Vec<_>, _>>()?;
//     // b_bit_vars is the least 15 bits of b
//     // (we only care for the first 15 bits of b_bits)
//     let b_bit_vars = b_bits
//         .iter()
//         .take(15)
//         .map(|x| Boolean::new_witness(cs.clone(), || Ok(x)))
//         .collect::<Result<Vec<_>, _>>()?;
//     enforce_decompose(a, a_bit_vars.as_ref())?;
//     enforce_decompose(b, b_bit_vars.as_ref())?;
//
//     // a == b if
//     // * a[i] == b[i] for i in [0..14], and
//     let a_i_is_eq_b_i = a_bit_vars
//         .iter()
//         .zip(b_bit_vars.iter())
//         .map(|(a_i, b_i)| a_i.is_eq(b_i))
//         .collect::<Result<Vec<_>, _>>()?;
//
//     Boolean::kary_and(a_i_is_eq_b_i.as_ref())
// }

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ed_on_bls12_381::fq::Fq;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{rand::Rng, test_rng, UniformRand};

    macro_rules! test_range_proof_12289 {
        ($value: expr, $satisfied: expr) => {
            let cs = ConstraintSystem::<Fq>::new_ref();
            let a = Fq::from($value);
            let a_var = FpVar::<Fq>::new_witness(cs.clone(), || Ok(a)).unwrap();

            enforce_less_than_12289(cs.clone(), &a_var).unwrap();
            assert_eq!(cs.is_satisfied().unwrap(), $satisfied);
            println!(
                "number of variables {} {} and constraints {}\n",
                cs.num_instance_variables(),
                cs.num_witness_variables(),
                cs.num_constraints(),
            );
        };
    }
    #[test]
    fn test_range_proof_12289() {
        // =======================
        // good path
        // =======================
        // the meaning of life
        test_range_proof_12289!(42, true);

        // edge case: 0
        test_range_proof_12289!(0, true);

        // edge case: 2^12
        test_range_proof_12289!(1 << 12, true);

        // edge case: 2^13
        test_range_proof_12289!(1 << 13, true);

        // edge case: 12288
        test_range_proof_12289!(12288, true);

        // =======================
        // bad path
        // =======================
        // edge case: 12289
        test_range_proof_12289!(12289, false);

        // edge case: 12290
        test_range_proof_12289!(12290, false);

        // edge case: 12290
        test_range_proof_12289!(122900000, false);

        // =======================
        // random path
        // =======================
        let mut rng = test_rng();
        for _ in 0..1000 {
            let t = rng.gen_range(0..1 << 15);
            test_range_proof_12289!(t, t < 12289);
        }

        // // the following code prints out the
        // // cost for arkworks native range proof
        // let cs = ConstraintSystem::<Fq>::new_ref();
        // let a = Fq::from(42);
        // let a_var = FpVar::<Fq>::new_witness(cs.clone(), || Ok(a)).unwrap();
        // let b_var = FpVar::<Fq>::new_constant(cs.clone(),
        // Fq::from(12289)).unwrap(); a_var.enforce_cmp(&b_var,Ordering:
        // :Less, false).unwrap(); println!(
        //     "number of variables {} {} and constraints {}\n",
        //     cs.num_instance_variables(),
        //     cs.num_witness_variables(),
        //     cs.num_constraints(),
        // );

        // assert!(false)
    }

    macro_rules! test_range_proof_norm_bound {
        ($value: expr, $satisfied: expr) => {
            let cs = ConstraintSystem::<Fq>::new_ref();
            let a = Fq::from($value);
            let a_var = FpVar::<Fq>::new_witness(cs.clone(), || Ok(a)).unwrap();

            enforce_less_than_norm_bound(cs.clone(), &a_var).unwrap();
            assert_eq!(cs.is_satisfied().unwrap(), $satisfied, "{}", $value);
            println!(
                "number of variables {} {} and constraints {}\n",
                cs.num_instance_variables(),
                cs.num_witness_variables(),
                cs.num_constraints(),
            );
        };
    }
    #[test]
    fn test_range_proof_norm_bound() {
        // =======================
        // good path
        // =======================
        // the meaning of life
        test_range_proof_norm_bound!(42, true);

        // edge case: 0
        test_range_proof_norm_bound!(0, true);

        // edge case: 2^25
        test_range_proof_norm_bound!(1 << 25, true);

        // edge case: 2^24
        test_range_proof_norm_bound!(1 << 24, true);

        // edge case: 34034725
        test_range_proof_norm_bound!(34034725, true);

        // =======================
        // bad path
        // =======================
        // edge case: 34034726
        test_range_proof_norm_bound!(34034726, false);

        // edge case: 34034727
        test_range_proof_norm_bound!(34034727, false);

        // edge case: 2^26
        test_range_proof_norm_bound!(1 << 26, false);

        // edge case: 2^27
        test_range_proof_norm_bound!(1 << 27, false);

        // =======================
        // random path
        // =======================
        let mut rng = test_rng();
        for _ in 0..1000 {
            let t = rng.gen_range(0..1 << 27);
            test_range_proof_norm_bound!(t, t < 34034726);
        }

        // // the following code prints out the
        // // cost for arkworks native range proof
        // let cs = ConstraintSystem::<Fq>::new_ref();
        // let a = Fq::from(42);
        // let a_var = FpVar::<Fq>::new_witness(cs.clone(), || Ok(a)).unwrap();
        // let b_var = FpVar::<Fq>::new_constant(cs.clone(),
        // Fq::from(12289)).unwrap(); a_var
        //     .enforce_cmp(&b_var, std::cmp::Ordering::Less, false)
        //     .unwrap();
        // println!(
        //     "number of variables {} {} and constraints {}\n",
        //     cs.num_instance_variables(),
        //     cs.num_witness_variables(),
        //     cs.num_constraints(),
        // );

        // assert!(false)
    }

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

    macro_rules! test_range_proof_6144 {
        ($value: expr, $satisfied: expr) => {
            let cs = ConstraintSystem::<Fq>::new_ref();
            let a = Fq::from($value);
            let a_var = FpVar::<Fq>::new_witness(cs.clone(), || Ok(a)).unwrap();

            let is_less = is_less_than_6144(cs.clone(), &a_var).unwrap();
            is_less.enforce_equal(&Boolean::TRUE).unwrap();
            assert_eq!(cs.is_satisfied().unwrap(), $satisfied);
            println!(
                "number of variables {} {} and constraints {}\n",
                cs.num_instance_variables(),
                cs.num_witness_variables(),
                cs.num_constraints(),
            );
        };
    }
    #[test]
    fn test_range_proof_6144() {
        // =======================
        // good path
        // =======================
        // the meaning of life
        test_range_proof_6144!(42, true);

        // edge case: 0
        test_range_proof_6144!(0, true);

        // edge case: 6143
        test_range_proof_6144!(6143, true);

        // =======================
        // bad path
        // =======================
        // edge case: 6144
        test_range_proof_6144!(6144, false);

        // edge case: 6145
        test_range_proof_6144!(6145, false);

        // edge case: 12289
        test_range_proof_6144!(12289, false);

        // =======================
        // random path
        // =======================
        let mut rng = test_rng();
        for _ in 0..1000 {
            let t = rng.gen_range(0..1 << 15);
            test_range_proof_6144!(t, t < 6144);
        }

        // // the following code prints out the
        // // cost for arkworks native range proof
        // let cs = ConstraintSystem::<Fq>::new_ref();
        // let a = Fq::from(42);
        // let a_var = FpVar::<Fq>::new_witness(cs.clone(), || Ok(a)).unwrap();
        // let b_var = FpVar::<Fq>::new_constant(cs.clone(),
        // Fq::from(12289)).unwrap(); a_var
        //     .enforce_cmp(&b_var, std::cmp::Ordering::Less, false)
        //     .unwrap();
        // println!(
        //     "number of variables {} {} and constraints {}\n",
        //     cs.num_instance_variables(),
        //     cs.num_witness_variables(),
        //     cs.num_constraints(),
        // );

        // assert!(false)
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
