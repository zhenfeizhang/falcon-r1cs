use ark_ed_on_bls12_381::fq::Fq;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, Field};
use ark_std::{rand::Rng, test_rng};
use falcon_r1cs::*;
use falcon_rust::{ntt, *};

fn main() {
    println!("                  # instance variables |      # witness |      #constraints |");
    count_ntt_conversion_constraints();
    count_verify_with_ntt_constraints();
    count_verify_with_schoolbook_constraints();
}

fn count_verify_with_schoolbook_constraints() {
    let keypair = KeyPair::keygen(9);
    let message = "testing message";
    let sig = keypair
        .secret_key
        .sign_with_seed("test seed".as_ref(), message.as_ref());

    assert!(keypair.public_key.verify(message.as_ref(), &sig));
    assert!(keypair
        .public_key
        .verify_rust_native_schoolbook(message.as_ref(), &sig));

    let cs = ConstraintSystem::<Fq>::new_ref();

    let falcon_circuit = FalconSchoolBookVerificationCircuit::build_circuit(
        keypair.public_key,
        message.to_string(),
        sig,
    );

    falcon_circuit.generate_constraints(cs.clone()).unwrap();
    println!(
        "verify with schoolbook:       {:8} |       {:8} |          {:8} |",
        cs.num_instance_variables(),
        cs.num_witness_variables(),
        cs.num_constraints(),
    );

    assert!(cs.is_satisfied().unwrap());
}

fn count_verify_with_ntt_constraints() {
    let keypair = KeyPair::keygen(9);
    let message = "testing message";
    let sig = keypair
        .secret_key
        .sign_with_seed("test seed".as_ref(), message.as_ref());

    assert!(keypair.public_key.verify(message.as_ref(), &sig));
    assert!(keypair
        .public_key
        .verify_rust_native_schoolbook(message.as_ref(), &sig));
    assert!(keypair
        .public_key
        .verify_rust_native_ntt(message.as_ref(), &sig));

    let cs = ConstraintSystem::<Fq>::new_ref();

    let falcon_circuit =
        FalconNTTVerificationCircuit::build_circuit(keypair.public_key, message.to_string(), sig);
    falcon_circuit.generate_constraints(cs.clone()).unwrap();
    println!(
        "verify with ntt:              {:8} |       {:8} |          {:8} |",
        cs.num_instance_variables(),
        cs.num_witness_variables(),
        cs.num_constraints(),
    );

    assert!(cs.is_satisfied().unwrap());
}

fn count_ntt_conversion_constraints() {
    let mut rng = test_rng();

    let cs = ConstraintSystem::<Fq>::new_ref();
    let param_var = ntt_param_var(cs.clone()).unwrap();
    let poly_u32 = (0..512)
        .map(|_| rng.gen_range(0..12289))
        .collect::<Vec<u32>>();
    let poly = poly_u32.iter().map(|x| Fq::from(*x)).collect::<Vec<Fq>>();
    let poly_var: Vec<FpVar<Fq>> = poly
        .iter()
        .map(|x| FpVar::<Fq>::new_witness(cs.clone(), || Ok(*x)).unwrap())
        .collect();

    // the [q, 2*q^2, 4 * q^3, ..., 2^9 * q^10] constant wires
    let const_12289_vars: Vec<FpVar<Fq>> = (1..11)
        .map(|x| {
            FpVar::<Fq>::new_constant(
                cs.clone(),
                Fq::from(1 << (x - 1)) * Fq::from(12289u16).pow(&[x]),
            )
            .unwrap()
        })
        .collect();
    let output = ntt(poly_u32.as_ref());

    let num_instance_variables = cs.num_instance_variables();
    let num_witness_variables = cs.num_witness_variables();
    let num_constraints = cs.num_constraints();

    let output_var = ntt_circuit(cs.clone(), &poly_var, &const_12289_vars, &param_var).unwrap();
    println!(
        "ntt conversion:               {:8} |       {:8} |          {:8} |",
        cs.num_instance_variables() - num_instance_variables,
        cs.num_witness_variables() - num_witness_variables,
        cs.num_constraints() - num_constraints,
    );

    for i in 0..512 {
        assert_eq!(Fq::from(output[i]), output_var[i].value().unwrap())
    }
}