# OPRF
This crate contains the protocols implemented for the Crypto Dark Matter OPRF Paper.
Three main protocols have been produced
- Fully malicious OPRF
- Client malicious OPRF
- Semi-honest OPRF

## Test and Benchmarks
To run tests of the OPRF and sub-protocols execute
```
cargo test
```
To run benchmarks of the OPRF or sub-protocols execute
```
cargo run --release --example bench_oprf
```
where `bench_oprf`can be replaced with any of the test in the folder `examples`

## Structure of code
The implementation of the protocol follows the protocol description from the paper.
The implementation can be found in the following files:
- Full malicious OPRF `{OPRF.rs}`
- Malicious client OPRF `{client_OPRF.rs}`
- Malicious client wPRF `{client_wPRF.rs}`
- candidate daBits based on Cut-n-Choose `{daBits_cnc_consistency.rs}`
- candidate daBits based on linear code `{daBits_code_consistency.rs}`
- Full daBits protocol `{dabits.rs}`
- Authenticated OLE over F3 `{F3triples.rs}`
- Full malicious wPRF `{full_wPRF.rs}`
- Half authenticated bits (haBits) `{habits.rs}`
- Input encoding utilities `{input_encoding.rs}`
- Semi-honest OPRF `{semi_OPRF.rs}`
- Semi-honest mod conversion bits `{ot_d_bits.rs}`
- Utilities `{matrix_util.rs, vole_util.rs}`