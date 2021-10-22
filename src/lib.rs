mod constants;
// mod errors;
mod gadgets;

use crate::gadgets::{
    enforce_less_than_12289, enforce_less_than_norm_bound, inner_product_mod, l2_norm_var,
};
use ark_ed_on_bls12_381::constraints::FqVar;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Result};
use falcon_rust::*;

pub struct FalconVerificationCircuit {
    pk: PublicKey,
    msg: String,
    sig: Signature,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for FalconVerificationCircuit {
    /// generate a circuit proving that for a given tuple: pk, msg, sig
    /// the following statement holds
    /// - hm = hash_message(message, nonce)     <- done in public
    /// - v = hm - sig * pk
    /// - l2_norm(sig, v) < SIG_L2_BOUND = 34034726
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<()> {
        let sig_poly = self.sig.unpack();
        let pk_poly = self.pk.unpack();
        let const_12289_var = FpVar::<F>::new_constant(cs.clone(), F::from(12289u16))?;

        // ========================================
        // compute related data in the clear
        // ========================================
        let hm = hash_message(self.msg.as_bytes(), self.sig.nonce().as_ref());
        // compute v = hm - uh and lift it to positives
        let uh = poly_mul(&pk_poly, &sig_poly);
        let mut v_pos = [0i16; 512];

        for (c, (&a, &b)) in v_pos.iter_mut().zip(uh.iter().zip(hm.iter())) {
            let c_i32 = (b as i32) + (a as i32);
            *c = (c_i32 % 12289) as i16;

            if *c < 0 {
                *c += 12289
            }
        }

        // ========================================
        // allocate the variables with range checks
        // ========================================
        // signature
        let mut sig_poly_vars = Vec::new();
        for e in sig_poly {
            let e = if e < 0 { e + 12289 } else { e } as u16;
            let tmp = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(e)))?;

            // ensure all the sig inputs are smaller than 12289
            enforce_less_than_12289(cs.clone(), &tmp)?;
            sig_poly_vars.push(tmp);
        }

        // pk
        //
        // here we use a buffer = [-pk[0], -pk[1], ..., -pk[511], pk[0], pk[1], ...,
        // pk[511]] where the buffer[i+1..i+513] will be used for the i-th
        // column in inner-product calculation
        let mut pk_poly_vars = Vec::new();
        let mut neg_pk_poly_vars = Vec::new();
        for e in pk_poly {
            // ensure all the pk inputs are smaller than 12289
            // pk is public input, does not need to keep secret
            let tmp = FpVar::<F>::new_input(cs.clone(), || Ok(F::from(e)))?;
            enforce_less_than_12289(cs.clone(), &tmp)?;
            // It is implied that all the neg_pk inputs are smaller than 12289
            neg_pk_poly_vars.push(&const_12289_var - &tmp);

            pk_poly_vars.push(tmp);
        }

        // hash of message
        let mut hm_vars = Vec::new();
        for e in hm.iter() {
            // ensure all the hm inputs are smaller than 12289
            // hm is public input, does not need to keep secret
            let tmp = FpVar::<F>::new_input(cs.clone(), || Ok(F::from(*e)))?;
            enforce_less_than_12289(cs.clone(), &tmp)?;
            hm_vars.push(tmp);
        }

        // v with positive coefficients
        let mut v_pos_vars = Vec::new();
        for e in v_pos {
            // ensure all the v inputs are smaller than 12289
            // v will need to be kept secret
            let tmp = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(e as u16)))?;
            enforce_less_than_12289(cs.clone(), &tmp)?;
            v_pos_vars.push(tmp);
        }

        // ========================================
        // proving v = hm + sig * pk mod 12289
        // ========================================
        // we are proving the polynomial congruence via
        // a school-bool vector-matrix multiplication.
        //
        // Two alternative approaches are
        // * FFT -- which itself requires one vector-matrix multiplication.
        // * Karatsuba -- which takes less multiplications but more additions,
        // and additions are also costly in our circuits representation.
        //
        // We will look into those options later.

        // build buffer = [-pk[0], -pk[1], ..., -pk[511], pk[0], pk[1], ..., pk[511]]
        let mut buf_poly_poly_vars = [neg_pk_poly_vars, pk_poly_vars].concat();
        buf_poly_poly_vars.reverse();

        for i in 0..512 {
            // current_col = sig * pk[i]
            let current_col = inner_product_mod(
                cs.clone(),
                sig_poly_vars.as_ref(),
                buf_poly_poly_vars[511 - i..1023 - i].as_ref(),
            )?;

            // right = hm + sig * pk[i]
            let rhs = &hm_vars[i] + &current_col;

            // v = rhs mod 12289
            (((&rhs).is_eq(&v_pos_vars[i])?)
                .or(&(&rhs).is_eq(&(&v_pos_vars[i] + &const_12289_var))?)?)
            .enforce_equal(&Boolean::TRUE)?;
        }

        // ========================================
        // proving l2_norm(v | sig) < 34034726
        // ========================================
        let l2_norm_var = l2_norm_var(cs.clone(), &[v_pos_vars, sig_poly_vars].concat())?;
        let l2_norm_bound_var = FpVar::<F>::new_constant(cs, F::from(34034726u64))?;
        // todo: complete this optimization to save 1000 constraints
        // enforce_less_than_norm_bound(cs, l2_norm_var)
        l2_norm_var.enforce_cmp(&l2_norm_bound_var, std::cmp::Ordering::Less, false)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use ark_ed_on_bls12_381::fq::Fq;
    use ark_relations::r1cs::ConstraintSystem;
    #[test]
    fn test_r1cs() {
        let keypair = KeyPair::keygen(9);
        let message = "testing message";
        let sig = keypair
            .secret_key
            .sign_with_seed("test seed".as_ref(), message.as_ref());

        assert!(keypair.public_key.verify(message.as_ref(), &sig));
        assert!(keypair
            .public_key
            .verify_rust_native(message.as_ref(), &sig));

        let cs = ConstraintSystem::<Fq>::new_ref();

        let falcon_circuit = FalconVerificationCircuit {
            pk: keypair.public_key,
            msg: message.to_string(),
            sig,
        };

        falcon_circuit.generate_constraints(cs.clone()).unwrap();
        println!(
            "number of variables {} {} and constraints {}\n",
            cs.num_instance_variables(),
            cs.num_witness_variables(),
            cs.num_constraints(),
        );

        assert!(cs.is_satisfied().unwrap());
        assert!(false)
    }
}
