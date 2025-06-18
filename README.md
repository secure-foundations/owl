# OwlC: Compiling Security Protocols to Verified, Secure, High-Performance Libraries

This repository contains the artifact for OwlC, an automatic compiler for security protocols written in the Owl language to verified implementations in Verus.

## Code structure

The source files are in `src/`. OwlC consists of the code in `src/Extraction` and `src/Pass`, while the remaining code is our updated version of the Owl typechecker.

OwlC outputs a library crate in `extraction/`. The generated code goes in `extraction/src/lib.rs`, while the other files are ancillary handwritten Verus code for the compiled library.

### Case studies

The 14 toy protocols from the original Owl work are in `owl_toy_protocols/`.

Our full WireGuard and HPKE case studies are in `full_protocol_case_studies/`. Within that directory: 
- `full_protocol_case_studies/owl_models/` contains the Owl source protocol models for each case study, and
- `full_protocol_case_studies/implementations` contains our interoperable WireGuard and HPKE executables, consisting of OwlC's generated library, along with reused components from off-the-shelf implementations and handwritten glue code for WireGuard.

Our example verified echo server is in `echo_server_example`.

### Evaluation scripts

The `Dockerfile` and the various `.py` scripts at the top level of this directory are to automate the evaluation workflows from our paper on OwlC. Please see the provided artifact evaluation appendix for details of how to use them.
