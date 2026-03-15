# Crypto Dark Matter OPRF

This repository contains the implementation for the paper "A Maliciously-Secure Post-Quantum OPRF from Crypto Dark Matter".
The results summarized here have been carried out under the research  policy agreement of [Cyberagentur's EC2 Program](https://www.cyberagentur.de/en/programs/ec2).

<img src="writeup/EC2_Icon.svg" alt="LOGO EC2" width="100"/>

The repository contains **prototype implementations** developed as part of the [MPCC](https://www.openmpcc.com/) project’s research and development activities.

<Link to MPCC>

All materials have been reviewed by intellectual property experts and cleared by the *Agentur für Innovation in der Cybersicherheit GmbH* for public release.

## Purpose

The goal of this repository is to:

* Provide **reference prototypes** demonstrating concepts, methods, or algorithms researched and developed during the **MPCC** project.
* Serve as a **technical starting point** for future development.
* Enables a community of collaborators, researchers, and developers to **explore, test, and extend** the prototype implementations.

## A note on security

Artefacts are currently considered **research prototypes** and not audited for security. Do not deploy it in
production, or entrust it with actual sensitive data as-is.

## Clearance

The content in this repository has been:

* Reviewed by the [IP experts](mailto:IP@cyberagentur.de?cc=ec2@cyberagentur.de?subject=MPCC) at *Agentur für Innovation in der Cybersicherheit GmbH*
* Approved for **public distribution and research use** according to the `LICENSE`.

Additions must undergo the clearance process before being merged into the main branch, unless explicitly agreed upon otherwise.

## Citing

If you use these results in your academic work, please cite it as follows:
```bibtex
@misc{MPCC-CDM-OPRF,
  title        = {{A Maliciously-Secure Post-Quantum OPRF from Crypto Dark Matter}},
  author       = {Diego F. Aranha and Aron van Baarsen and Adam Blatchley Hansen and Kent Nielsen and Peter Scholl},
  year         = 2025,
  month        = {October},
  howpublished = {https://github.com/dfaranha/Crypto-Dark-Matter-OPRF-minimal},
}
```

## Tests
To run the test for the OPRF, go into the `oprf` folder and run the following command
```
	cargo test
```
This test will take around 2 minutes and test that all OPRF protocols alongside the subprotocols are working as expected.

If you want to test the full swanky implementation run the `cargo test` command in the root folder. Sub-crates containing Field Arithmetics, VOLE expansion or High-degree ZK proof can be tested in `scuttlebutt`, `ocelot` and `diet-mac-and-cheese` respectively.

## Benchmarks
To run the benchmarks of the OPRF, go into the `oprf` folder and rne the following command
```
	cargo run --release --example bench_oprf
```
Here `bench_oprf` denotes the OPRF benchmarks.
All the benchmarks can be found in `oprf/examples`.
The most important benchmarks are the `bench_oprf`, `bench_c_oprf` and `bench_semi_oprf` which benchmarks the fully-malicious, client-malicious and semi-honest OPRF protocols.

These three benchmarks will produce the output
```
	C-off-time, C-on-time, C-comm, S-off-time, S-on-time, S-comm
```
Where `C` denotes the client and `S` denotes the server. The units are `us` and `Bits`. 

## Structure

*Note: All parts of the repository not mentioned have not been altered and are part of the public [Swanky](https://github.com/GaloisInc/swanky) library

The implementation of the protocols can be found in 
```oprf/src/*```

The field implementation for $F_3$ can be found in
```scuttlebutt/src/field/{f3, f64t}.rs```

The field implementation for $F_{2^{256}}$ can be found in
```scuttlebutt/src/field/f256b.rs```

Optimizations to the VOLE extension protocol are placed in
`ocelot/src/svole/wykw/svole.rs`

The high-degree ZK proof protocol can be found in
`diet-mac-and-cheese/src/hd_quicksilver.rs`
This is a direct fork of [Vole-ZK-Conversions](https://github.com/AarhusCrypto/vole-zk-conversions)

The PQ base OT implementation can be found in
`ocelot/src/ot/endemic_ot.rs`.
This is based on a kyber implementation found in
`kyber_ot`
This implementation is direct fork of [Argyle-Software Kyber](https://github.com/Argyle-Software/kyber)

## Contributing

Contributions are welcome, when following these requirements:

* Code must be **self-contained** and free of sensitive data.
* Documentation must clearly explain purpose and usage.
* All contributions **must undergo review** before merging.
* Follow internal coding and documentation standards (see `usage.md`).

To propose a contribution:

1. Fork the repository
2. Create a feature branch
3. Submit a pull request

If you have questions related to the prototypes or need technical clarification, please open an issue in the repository or contact the project maintainers.

## License

This repository is distributed under [License](./LICENSE), unless otherwise specified.

## Acknowledgement

This work has been supported by funding from *Agentur für Innovation in der Cybersicherheit GmbH*.

## Contact

You can contact the `OpenMPCC` team at `cyberagentur-group@enclaive.io`.
