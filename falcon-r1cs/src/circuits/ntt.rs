use crate::gadgets::*;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Result};
use falcon_rust::*;

#[derive(Clone, Debug)]
pub struct FalconNTTVerificationCircuit {
    pk: PublicKey,
    msg: Vec<u8>,
    sig: Signature,
}

impl FalconNTTVerificationCircuit {
    pub fn build_circuit(pk: PublicKey, msg: Vec<u8>, sig: Signature) -> Self {
        Self { pk, msg, sig }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for FalconNTTVerificationCircuit {
    /// generate a circuit proving that for a given tuple: pk, msg, sig
    /// the following statement holds
    /// - hm = hash_message(message, nonce)     <- done in public
    /// - v = hm - sig * pk
    /// - l2_norm(sig, v) < SIG_L2_BOUND = 34034726
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<()> {
        let sig_poly: Polynomial = (&self.sig).into();
        let pk_poly: Polynomial = (&self.pk).into();

        // the [q, 2*q^2, 4 * q^3, ..., 2^9 * q^10] constant wires
        let const_q_power_vars: Vec<FpVar<F>> = (1..LOG_N + 2)
            .map(|x| {
                FpVar::<F>::new_constant(
                    cs.clone(),
                    F::from(1u32 << (x - 1)) * F::from(MODULUS).pow(&[x as u64]),
                )
                .unwrap()
            })
            .collect();
        let param_vars = ntt_param_var(cs.clone()).unwrap();
        // ========================================
        // compute related data in the clear
        // ========================================
        let hm = Polynomial::from_hash_of_message(self.msg.as_ref(), self.sig.nonce());
        let hm_ntt = NTTPolynomial::from(&hm);

        // compute v = hm + uh and lift it to positives
        let uh = sig_poly * pk_poly;
        let v = uh + hm;

        let pk_ntt = NTTPolynomial::from(&pk_poly);

        // ========================================
        // allocate the variables with range checks
        // ========================================
        // signature
        let mut sig_poly_vars = Vec::new();
        for &e in sig_poly.coeff() {
            let tmp = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(e)))?;

            // ensure all the sig inputs are smaller than MODULUS
            // Note that this step is not necessary: we will be checking
            // the l2-norm of \|sig | v\| < 34034726. If any
            // coefficient of sig is greater than MODULUS, we will have
            // a l2-norm that is at least > MODULUS^2 which is greater
            // than 34034726 and cause the circuit to be unsatisfied.
            //
            // enforce_less_than_q(cs.clone(), &tmp)?;
            sig_poly_vars.push(tmp);
        }
        // pk, in the NTT form
        //
        let mut pk_ntt_vars = Vec::new();
        for &e in pk_ntt.coeff() {
            // do not need to ensure the pk inputs are smaller than MODULUS
            // pk is public input, so the verifier can check in the clear
            pk_ntt_vars.push(FpVar::<F>::new_input(cs.clone(), || Ok(F::from(e)))?);
        }
        // hash of message in the NTT format
        // public input
        let mut hm_ntt_vars = Vec::new();
        for e in hm_ntt.coeff() {
            // do not need to ensure the hm inputs are smaller than MODULUS
            // hm is public input, does not need to keep secret
            hm_ntt_vars.push(FpVar::<F>::new_input(cs.clone(), || Ok(F::from(*e)))?);
        }
        // v with positive coefficients
        let mut v_pos_vars = Vec::new();
        for e in v.coeff() {
            // ensure all the v inputs are smaller than MODULUS
            // v will need to be kept secret
            let tmp = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(*e)))?;
            enforce_less_than_q(cs.clone(), &tmp)?;
            v_pos_vars.push(tmp);
        }
        // ========================================
        // proving v = hm + sig * pk mod MODULUS
        // ========================================
        // we are proving the polynomial congruence via NTT.
        //

        // first, prove that the circuit variable are indeed the
        // NTT representation of the polynomial
        //  sig_ntt_vars = ntt_circuit(sig_vars)
        //  v_ntt_vars = ntt_circuit(v_vars)
        let sig_ntt_vars =
            ntt_circuit(cs.clone(), &sig_poly_vars, &const_q_power_vars, &param_vars)?;
        let v_ntt_vars = ntt_circuit(cs.clone(), &v_pos_vars, &const_q_power_vars, &param_vars)?;

        // second, prove the equation holds in the ntt domain
        for i in 0..N {
            // v[i] = hm[i] + sig[i] * pk[i] % MODULUS

            // println!(
            //     "{:?} {:?} {:?} {:?}",
            //     v_ntt_vars[i].value()?.into_repr(),
            //     hm_ntt_vars[i].value()?.into_repr(),
            //     sig_ntt_vars[i].value()?.into_repr(),
            //     pk_ntt_vars[i].value()?.into_repr(),
            // );

            v_ntt_vars[i].enforce_equal(&add_mod(
                cs.clone(),
                &hm_ntt_vars[i],
                &(&sig_ntt_vars[i] * &pk_ntt_vars[i]),
                &const_q_power_vars[0],
            )?)?;
        }

        // ========================================
        // proving l2_norm(v | sig) < 34034726
        // ========================================
        let l2_norm_var = l2_norm_var(
            cs.clone(),
            &[v_pos_vars, sig_poly_vars].concat(),
            &const_q_power_vars[0],
        )?;

        enforce_less_than_norm_bound(cs, &l2_norm_var)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use ark_ed_on_bls12_381::fq::Fq;
    use ark_relations::r1cs::ConstraintSystem;
    #[test]
    fn test_ntt_verification_r1cs() {
        let keypair = KeyPair::keygen();
        let message = "testing message".as_bytes();
        let sig = keypair
            .secret_key
            .sign_with_seed("test seed".as_ref(), message.as_ref());

        assert!(keypair.public_key.verify(message.as_ref(), &sig));
        assert!(keypair.public_key.verify_rust(message.as_ref(), &sig));

        let cs = ConstraintSystem::<Fq>::new_ref();

        let falcon_circuit = FalconNTTVerificationCircuit {
            pk: keypair.public_key,
            msg: message.to_vec(),
            sig,
        };

        falcon_circuit.generate_constraints(cs.clone()).unwrap();
        // println!(
        //     "number of variables {} {} and constraints {}\n",
        //     cs.num_instance_variables(),
        //     cs.num_witness_variables(),
        //     cs.num_constraints(),
        // );

        assert!(cs.is_satisfied().unwrap());
    }
}
