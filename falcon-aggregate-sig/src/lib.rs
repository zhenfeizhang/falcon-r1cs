use aggregated_signature_circuit::FalconAggregateSignatureCircuit;
use ark_bls12_381::{Bls12_381, Fr};
use ark_crypto_primitives::SNARK;
use ark_groth16::{create_random_proof, verify_proof, Groth16, PreparedVerifyingKey};
use falcon_rust::{hash_message, ntt, KeyPair, PublicKey, SecretKey, Signature, N};
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};
pub struct FalconAggregateableSignatureScheme;

mod aggregated_signature_circuit;

pub trait AggregateableSignature {
    type SigningKey;
    type VerificationKey;
    type PublicParameter;
    type Signature;
    type AggregatedSignature;

    /// Generate the public parameters for aggregation for x number of
    /// aggregations
    fn pp_gen(seed: [u8; 32], len: usize) -> Self::PublicParameter;

    /// Generate a pair of keys from a seed
    fn key_gen(seed: [u8; 32]) -> (Self::SigningKey, Self::VerificationKey);

    /// Sign a message with a signing key and a random seed
    fn sign(seed: [u8; 32], sk: &Self::SigningKey, message: &[u8]) -> Self::Signature;

    /// Verify a signature for a message with a verification key
    fn verify(vk: &Self::VerificationKey, message: &[u8], signature: &Self::Signature) -> bool;

    /// aggregate a set of signatures
    fn aggregate(
        seed: [u8; 32],
        vks: &[Self::VerificationKey],
        messages: &[&[u8]],
        signatures: &[Self::Signature],
        pp: &Self::PublicParameter,
    ) -> Self::AggregatedSignature;

    /// batch_verifies an aggregated signature, given the messages and the
    /// verification keys
    fn batch_verify(
        vks: &[Self::VerificationKey],
        messages: &[&[u8]],
        signature: &Self::AggregatedSignature,
        pp: &Self::PublicParameter,
    ) -> bool;
}

impl AggregateableSignature for FalconAggregateableSignatureScheme {
    type SigningKey = SecretKey;
    type VerificationKey = PublicKey;
    type PublicParameter = <Groth16<Bls12_381> as SNARK<Fr>>::ProvingKey;
    type Signature = Signature;
    type AggregatedSignature = <Groth16<Bls12_381> as SNARK<Fr>>::Proof;

    /// Generate the public parameters for aggregation for x number of
    /// aggregations
    fn pp_gen(seed: [u8; 32], len: usize) -> Self::PublicParameter {
        let mock_kp = Self::key_gen([0; 32]);
        let mock_msg = "This is the message for testing".as_bytes();
        let mock_sig = mock_kp.0.sign(mock_msg.as_ref());

        // let cs = ConstraintSystem::<Fr>::new_ref();

        let falcon_aggregate_signature_circuit = FalconAggregateSignatureCircuit {
            vks: &vec![mock_kp.1; len],
            messages: &vec![mock_msg; len],
            signatures: &vec![mock_sig; len],
        };

        Groth16::circuit_specific_setup(
            falcon_aggregate_signature_circuit,
            &mut ChaCha20Rng::from_seed(seed),
        )
        .unwrap()
        .0
    }

    /// Generate a pair of keys from a seed
    fn key_gen(seed: [u8; 32]) -> (Self::SigningKey, Self::VerificationKey) {
        let keypair = KeyPair::keygen_with_seed(&seed);
        (keypair.secret_key, keypair.public_key)
    }

    /// Sign a message with a signing key and a random seed
    fn sign(seed: [u8; 32], sk: &Self::SigningKey, message: &[u8]) -> Self::Signature {
        sk.sign_with_seed(seed.as_ref(), message)
    }

    /// Verify a signature for a message with a verification key
    fn verify(vk: &Self::VerificationKey, message: &[u8], signature: &Self::Signature) -> bool {
        vk.verify(message, signature)
    }

    /// aggregate a set of signatures
    fn aggregate(
        seed: [u8; 32],
        vks: &[Self::VerificationKey],
        messages: &[&[u8]],
        signatures: &[Self::Signature],
        pp: &Self::PublicParameter,
    ) -> Self::AggregatedSignature {
        let falcon_aggregate_signature_circuit = FalconAggregateSignatureCircuit {
            vks,
            messages,
            signatures,
        };

        create_random_proof(
            falcon_aggregate_signature_circuit,
            pp,
            &mut ChaCha20Rng::from_seed(seed),
        )
        .unwrap()
    }

    /// batch_verifies an aggregated signature, given the messages and the
    /// verification keys
    fn batch_verify(
        vks: &[Self::VerificationKey],
        messages: &[&[u8]],
        signature: &Self::AggregatedSignature,
        pp: &Self::PublicParameter,
    ) -> bool {
        let pvk = PreparedVerifyingKey::from(pp.vk.clone());

        // parse the input
        let hm_ntts: Vec<[u32; N]> = messages
            .iter()
            .map(|msg| {
                ntt(&hash_message(msg.as_ref(), [0; 40].as_ref())
                    .iter()
                    .map(|x| *x as u32)
                    .collect::<Vec<u32>>())
            })
            .collect();

        let vk_ntts: Vec<[u32; N]> = vks
            .iter()
            .map(|x| ntt(&x.unpack().iter().map(|x| *x as u32).collect::<Vec<u32>>()))
            .collect();

        let mut inputs = Vec::new();
        for (hm, vk) in hm_ntts.iter().zip(vk_ntts.iter()) {
            for e in vk {
                inputs.push(Fr::from(*e))
            }
            for e in hm {
                inputs.push(Fr::from(*e))
            }
        }

        // verifies the ZKP
        let res =
        verify_proof(&pvk, signature, &inputs);
        println!("res: {:?}", res);
        res.unwrap()
    }
}

#[cfg(test)]
mod tests {
    use ark_std::{rand::RngCore, test_rng};

    use super::*;

    #[test]
    fn test_aggregated_signature() {
        let mut rng = test_rng();
        let mut seed = [0u8; 32];

        let mut vks = Vec::new();

        let mut messages = Vec::new();

        let mut signatures = Vec::new();

        for i in 0..2 {
            rng.fill_bytes(&mut seed);

            let keypair = FalconAggregateableSignatureScheme::key_gen(seed);
            let message = format!("testing message {}", i);

            rng.fill_bytes(&mut seed);
            let signature =
                FalconAggregateableSignatureScheme::sign(seed, &keypair.0, message.as_ref());

            assert!(FalconAggregateableSignatureScheme::verify(
                &keypair.1,
                message.as_ref(),
                &signature
            ));

            vks.push(keypair.1);
            messages.push(message);
            signatures.push(signature)
        }

        let messages_ref: Vec<&[u8]> = messages.iter().map(|x| x.as_bytes()).collect();

        println!("key generation");
        rng.fill_bytes(&mut seed);
        let pp = FalconAggregateableSignatureScheme::pp_gen(seed, 2);

        println!("aggregation");

        rng.fill_bytes(&mut seed);
        let agg_sig = FalconAggregateableSignatureScheme::aggregate(
            seed,
            &vks,
            &messages_ref,
            &signatures,
            &pp,
        );

        println!("batch verification");
        assert!(FalconAggregateableSignatureScheme::batch_verify(
            &vks,
            &messages_ref,
            &agg_sig,
            &pp
        ));

        println!("finished");
    }
}
