use ark_ff::PrimeField;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Result};
use falcon_r1cs::FalconNTTVerificationCircuit;
use falcon_rust::{PublicKey, Signature};

#[derive(Clone, Debug)]
pub struct FalconAggregateSignatureCircuit<'a> {
    pub vks: &'a [PublicKey],
    pub messages: &'a [&'a [u8]],
    pub signatures: &'a [Signature],
}

impl<F: PrimeField> ConstraintSynthesizer<F> for FalconAggregateSignatureCircuit<'_> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<()> {
        for (&vk, (&message, &signature)) in self
            .vks
            .iter()
            .zip(self.messages.iter().zip(self.signatures.iter()))
        {
            let falcon_circuit =
                FalconNTTVerificationCircuit::build_circuit(vk, message.to_vec(), signature);
            falcon_circuit.generate_constraints(cs.clone()).unwrap();
        }

        println!("circuit satisfied? {:?}", cs.is_satisfied());
        Ok(())
    }
}
