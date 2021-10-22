Falcon R1CS
-----

This crate generates the R1CS circuit for Falcon signature verifications.

# Performance

The total #constraints for a single Falcon-512 signature verification is listed
below. The table can be obtained via
```
cargo run --release --example constraint_counts
```

|                 | # instance variables |      # witness |      #constraints |
|---|---:|---:|---:|
|ntt conversion|                      0 |          81664 |             84480 |
|verify with ntt|                  1025 |         212018 |            219700 |
|verify with schoolbook|           1025 |         312882 |            315956 |



In comparison, an ECC scalar multiplication over Jubjub curve (\~256 bits) takes a little over __3k__ constraints (example [here](https://github.com/zhenfeizhang/bandersnatch/blob/main/bandersnatch/examples/constraint_count_jubjub.rs)).
So this will be something like 35\~50 times more costly than proving, say, Schnorr over Jubjub curve.

# Pseudocode for NTT based verification

```
// signature; requires 1 ntt conversion circuit
u := sig
u_var = u.into_circuit()
u_ntt_var = ntt_circuit(u)

// public key; no ntt conversion circuit is required
h := pk              
h_ntt = ntt(h)                    
h_ntt_var = h_ntt.into_circuit()

// hash of the message; no ntt conversion circuit is required
hm = hash_message(msg, nonce) 
hm_ntt = ntt(hm)
hn_ntt_var = hm_ntt.into_circuit()

// compute v = hm + u * h in the clear
v =  hm + u * h

// compute v = hm + u * h with circuit
v_ntt_var = hm_ntt_var + u_ntt_var * h_ntt_var

// enforce v_ntt_var is indeed v, requires 1 ntt conversion
v_var = v.into_circuit()
v_ntt_var.is_equal( ntt_circuit(v_var) )

// enforce the l2 norm constraints
l2_norm_var = compute_l2_norm(v_var, u_var)
l2_nrom_var.is_smaller( L2_NORM_BOUND )
```