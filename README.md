# SMT Encoding of TLA+: Modules and Benchmarks

You will find in `specs/` the TLA+ modules with proofs and in `benchs.tar.gz` the SMT problems that were generated from them.

To generate the SMT benchmarks, TLAPS was called on each specification with the following commands:
```{bash}
# Use the old SMT backend -- we generate two versions, with and without type synthesis
tlapm -I TheSpec.tla --toolbox 0 0 --nofp --stretch 0.1 --method smt --debug oldsmt,types0,tempfiles
tlapm -I TheSpec.tla --toolbox 0 0 --nofp --stretch 0.1 --method smt --debug oldsmt,types1,tempfiles

# Use the new SMT backend
tlapm -I TheSpec.tla --toolbox 0 0 --nofp --stretch 0.1 --method smt --debug t0,tempfiles
```

The exact version of TLAPS that was used for the experiment in available at https://github.com/tlaplus/tlapm/tree/smt-changes.

Our specifications are taken from three sources:
- The **TLA+ Examples**, which can be found at https://github.com/tlaplus/Examples
- The **TLAPS Examples**, which can be found with the distribution
- The **Deconstructed Bakery** specification, courtesy of Leslie Lamport and Stephan Merz

### Generating the SMT Benchmarks

If you want to generate the SMT benchmarks from the TLA+ specifications, we provide the script `gen.sh` to help.  This script must be invoked with a TLA+ specification as first argument and a configuration file as second argument -- configurations files are given in the `tlaps_conf` directory.  You will also need to provide the paths to TLAPS's directory and the TLA+ Community Modules directory on your computer, as third and fourth argument.

The following bash command will call `gen.sh` on every specificaction for every configuration:
```{bash}
for conf in tlaps_confs/*; do find specs/ -name '*.tla' -exec ./gen.sh {} "$conf" path_to_tlaps path_to_community_modules \; ; done
```

