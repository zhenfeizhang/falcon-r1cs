use super::*;
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

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

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ed_on_bls12_381::fq::Fq;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{rand::Rng, test_rng};

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
}
