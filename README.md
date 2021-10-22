Falcon R1CS
-----

This crate generates the R1CS circuit for Falcon signature verifications.

# Performance

The total #constraints for a single Falcon-512 signature verification is around __345k__ constraints. 
In comparison, an ECC scalar multiplication over Jubjub curve (~256 bits) takes a little over __3k__ constraints (example [here](https://github.com/zhenfeizhang/bandersnatch/blob/main/bandersnatch/examples/constraint_count_jubjub.rs)).
So this will be something like 50 times more costly than proving, say, Schnorr over Jubjub curve.

## Breakdown
This is mainly due to the fact that we need to simulate a non-native field arithmetics, for example each `c = a * b mod 12289` statement takes around 30 constraints. As a sanity check, this 345k constraints is broken down to

- multiplication takes 277 k constraints
  - each inner-product of 512 vectors takes 512 + 29 constraints
  - there are 512 inner-products which takes 277 k
- range proofs takes 43 k constraints
  - each range proof takes some 28 constraints
  - we need to prove range of 3 polynomials, that is 1536 range proofs
- the rest takes some 25 k constraints, including intermediate range checks, equality checks, etc.

