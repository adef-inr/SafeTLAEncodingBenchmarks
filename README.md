# SMT Encoding of TLA+: Modules and Benchmarks

You will find in `specs/` the TLA+ modules with proofs and in `benchs/` the SMT problems that were generated from them.

To generate the SMT benchmarks, TLAPS was called on each specification with the following commands:
```{bash}
# Use the old SMT backend
tlapm -I TheSpec.tla --toolbox 0 0 --nofp --method smt --debug oldsmt,types0,lia,tempfiles

# Use the new SMT backend
tlapm -I TheSpec.tla --toolbox 0 0 --nofp --method smt --debug newsmt,t0,lia,rwsetext,tempfiles
```

The exact version of TLAPS that was used for the experiment in available at https://github.com/tlaplus/tlapm/tree/encode.

The available specifications are:
- `Bakery/DeconProof.tla` --- The Deconstructed Bakery with a proof of mutual exclusion
- `Refinement/DistRefines.tla` --- Distributed version of the previous specification with a proof of refinement

The remaining specifications are duplicates of the above ones, with fewer but harder proof obligations.

- `Bakery/DeconProofShort.tla`
- `Refinement/DistRefinesShort.tla`
