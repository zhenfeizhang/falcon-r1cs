mod constants;
mod errors;
mod gadgets;

use crate::gadgets::{inner_product_mod, is_less_than_12289};
use ark_crypto_primitives::{
    commitment::pedersen::Randomness,
    prf::{blake2s::constraints::Blake2sGadget, PRFGadget},
    CommitmentGadget, PathVar,
};
use ark_ed_on_bls12_381::{constraints::FqVar, EdwardsProjective, Fq, Fr};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::*};
use ark_relations::{
    ns,
    r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Field, Result,
        SynthesisError, ToConstraintField,
    },
};
use ark_serialize::CanonicalDeserialize;
use falcon_rust::*;
use num_bigint::BigUint;

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
            is_less_than_12289(cs.clone(), &tmp)?;
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
            is_less_than_12289(cs.clone(), &tmp)?;
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
            is_less_than_12289(cs.clone(), &tmp)?;
            hm_vars.push(tmp);
        }

        // v with positive coefficients
        let mut v_pos_vars = Vec::new();
        for e in v_pos {
            // ensure all the v inputs are smaller than 12289
            // v will need to be kept secret
            let tmp = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(e as u16)))?;
            is_less_than_12289(cs.clone(), &tmp)?;
            v_pos_vars.push(tmp);
        }

        // ========================================
        // proving v = hm + sig * pk mod 12289
        // ========================================
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

        Ok(())
    }
}

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
    // assert!(false)
}
