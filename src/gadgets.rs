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
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    if a.len() == 0 || b.len() == 0 {
        panic!("Invalid input length: a {} vs b {}", a.len(), b.len());
    }

    b.iter()
        .map(|&b_i| inner_product_mod(cs.clone(), a, b_i))
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
) -> Result<FpVar<F>, SynthesisError> {
    if a.len() != b.len() || a.len() == 0 {
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
    let modulus_val = F::from(modulus_int);

    // cast the variables
    let modulus_var = FpVar::<F>::new_constant(cs.clone(), modulus_val)?;
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
    a: FpVar<F>,
    b: FpVar<F>,
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
    let modulus_val = F::from(modulus_int);

    // cast the variables
    let modulus_var = FpVar::<F>::new_constant(cs.clone(), modulus_val)?;
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
    //
    // if a_val >= F::from(12289u64) {
    //     return Err(FalconR1CSError::InvalidParameters(
    //         format!("Invalid input: {}", a_val).to_string(),
    //     ));
    // }

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

    // argue that a < 12289 = 2^13 + 2^12 + 1 via the following:
    // if a[13] == 0 return true
    // else if a[13] == 1 && a[12] == 0 return true
    // else if a[13] == 1 && a[12] == 1, a[11] && a[10] && ... && a[0] == 0 return
    // true else return false

    // a[13] == 0
    (a_bit_vars[13].not())
        // a[12] == 0
        .or(&a_bit_vars[12]
            .not()
            // a[11]^2 + ... a[0]^2 == 0
            .or(&Boolean::kary_or(a_bit_vars[0..11].as_ref())?.not())?)?
        .enforce_equal(&Boolean::TRUE)?;

    Ok(())
}

/// Constraint that the witness of a is smaller than 34034726
/// Cost: TBD constraints.
/// (This improves the range proof of 1264 constraints as in Arkworks.)
pub(crate) fn enforce_less_than_norm_bound<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &FpVar<F>,
) -> Result<(), SynthesisError> {
    // the norm bound is 0b10000001110101010000100110 which is 26 bits, i.e.,
    // 2^25 + 2^18 + 2^17 + 2^16 + 2^14 + 2^ 12 + 2^10 + 2^5 + 2^2 + 2

    let a_val = a.value()?;

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
    // // if a[25] == 0 return true
    // // else if
    // //    a[19..24] == 0  and a[13] == 1 && a[12] == 0 return true
    // // else if a[13] == 1 && a[12] == 1, a[11] && a[10] && ... && a[0] == 0
    // return // true else return false

    // // a[13] == 0
    // (a_bit_vars[13].not())
    //     // a[12] == 0
    //     .or(&a_bit_vars[12]
    //         .not()
    //         // a[11]^2 + ... a[0]^2 == 0
    //         .or(&Boolean::kary_or(a_bit_vars[0..11].as_ref())?.not())?)?
    //     .enforce_equal(&Boolean::TRUE)?;

    Ok(())
}

/// Return a variable indicating if the input is less than 6144 or not
/// Cost: TBD constraints.
/// (This improves the range proof of XXX constraints as in Arkworks.)
pub(crate) fn is_less_than_6144<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &FpVar<F>,
) -> Result<Boolean<F>, SynthesisError> {
    let a_val = a.value()?;

    // suppressing this check so that unit test can test
    // bad paths
    //
    // if a_val >= F::from(12289u64) {
    //     return Err(FalconR1CSError::InvalidParameters(
    //         format!("Invalid input: {}", a_val).to_string(),
    //     ));
    // }

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
    // a[13] == 0 and
    // either a[12] == 0 or a[11] == 0

    // a[13] == 0
    (a_bit_vars[13].not())
        // a[12] == 0
        .and(&a_bit_vars[12]
            .not()
            // a[11] == 0
            .or(&a_bit_vars[11].not())?)?
        .is_eq(&Boolean::TRUE)
}

/// Constraint that a = bits[0] + 2 bits[1] + 2^2 bits[2] ...
fn enforce_decompose<F: PrimeField>(
    a: &FpVar<F>,
    bits: &[Boolean<F>],
) -> Result<(), SynthesisError> {
    if bits.len() == 0 {
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
) -> Result<FpVar<F>, SynthesisError> {
    let const_12289_var = FpVar::<F>::new_constant(cs.clone(), F::from(12289u16))?;

    let mut res = FpVar::<F>::conditionally_select(
        &is_less_than_6144(cs.clone(), &input[0])?,
        &input[0],
        &(&const_12289_var - &input[0]),
    )?;
    res = &res * &res;
    for e in input.iter().skip(1) {
        let tmp = FpVar::<F>::conditionally_select(
            &is_less_than_6144(cs.clone(), e)?,
            e,
            &(&const_12289_var - e),
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

    macro_rules! test_range_proof {
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
        test_range_proof!(42, true);

        // edge case: 0
        test_range_proof!(0, true);

        // edge case: 12288
        test_range_proof!(12288, true);

        // =======================
        // bad path
        // =======================
        // edge case: 12289
        test_range_proof!(12289, false);

        // edge case: 12290
        test_range_proof!(12290, false);

        // edge case: 12290
        test_range_proof!(122900000, false);

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

    macro_rules! test_mul_mod {
        ($a:expr, $b:expr, $c:expr, $satisfied:expr) => {
            let cs = ConstraintSystem::<Fq>::new_ref();
            let a = Fq::from($a);
            let b = Fq::from($b);
            let c = Fq::from($c);

            let a_var = FpVar::<Fq>::new_witness(cs.clone(), || Ok(a)).unwrap();
            let b_var = FpVar::<Fq>::new_witness(cs.clone(), || Ok(b)).unwrap();

            let num_instance_variables = cs.num_instance_variables();
            let num_witness_variables = cs.num_witness_variables();
            let num_constraints = cs.num_constraints();

            let c_var = mul_mod(cs.clone(), a_var, b_var).unwrap();
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

            let num_instance_variables = cs.num_instance_variables();
            let num_witness_variables = cs.num_witness_variables();
            let num_constraints = cs.num_constraints();

            let c_var = inner_product_mod(cs.clone(), a_var.as_ref(), b_var.as_ref()).unwrap();
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

                let b_var_ref: Vec<&[FpVar<Fq>]> = b_var.iter().map(|x| x.as_ref()).collect();

                let num_instance_variables = cs.num_instance_variables();
                let num_witness_variables = cs.num_witness_variables();
                let num_constraints = cs.num_constraints();

                let c_var =
                    vector_matrix_mul_mod(cs.clone(), a_var.as_ref(), b_var_ref.as_ref()).unwrap();
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
