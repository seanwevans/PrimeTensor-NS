# H³ critical upstream proof-chain refactor: Pilot 2

Base: locally verified checkpoint `bac9c73d` (`refactor/h3-critical-gradient-pilot`).

This pilot is an explicitly mechanical migration of the following connected chain:

1. `Critical/Spectral/EnergyGate.lean`: all-orders radial cost and actual spectral H³ energy escape.
2. `Critical/Transport/SignedGrowthGate.lean`: transfer from spectral energy escape to nonintegrable signed physical H³ growth.
3. `Critical/Transport/PointwiseSignedTransport.lean`: existence of genuine intermediate positive signed physical transport.

The three original Control paths are replaced by imports forwarding to canonical modules. Internal imports along this three-module chain point to new canonical module names. Unmigrated downstream code continues importing the old paths, preserving its API. Pilot 1's four canonical modules, compatibility shims, body-hash manifest and baseline checker remain untouched.

All non-import lines are preserved byte-for-byte as Unicode text. The generated `critical-transport-path-map.json` stores source hashes, proof body hashes, and canonical import lists, with a checker invoked from the preexisting baseline. The script also checks uncovered modules, missing project imports, and the generated proof index. It refuses to apply over modified tracked source/index/baseline files.

Run `python3 tools/refactor/critical_transport_pilot.py --dry-run` (or omit the mode). Explicit `--apply` migrates source files and refreshes the source index but **does not compile Lean, commit, merge, or push**. `--check` checks the resulting migration. Run the pinned-toolchain Lake and repository baseline afterward.

For this pilot, `--apply` expects HEAD to be `bac9c73d` and that the Pilot 1 manifest and baseline hook exist. `--allow-different-head` is an intentional override, not the default.

A successful migration demonstrates proof-body preservation and compilation compatibility; it does not remove the higher radial moment, source ceiling, cutoff, terminal clock or other assumptions from the existing critical escape theorems. It proves no unconditional Navier–Stokes singularity claim.

This second pilot begins a common `module_migration.py` engine; Pilot 1's validated tool remains unchanged. Any later conversion of Pilot 1 to the shared engine must be independently reviewed.
