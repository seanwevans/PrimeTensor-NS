# Consolidation checkpoint

The build/contract baseline was committed as `1c4104d6` on 8 October 2026 UTC
(7 October in America/New_York). The user supplied a successful local fresh
project build: 22,161 jobs, successful root and contract elaboration, and a
zero exit status through commit and push. Dependency caches could be reused;
this was not a fresh rebuild of Lean and all mathlib dependencies.

The four audited continuation/restart theorems reported only `propext`,
`Classical.choice`, and `Quot.sound`. The finite theorem `h3JetIndex_card`
also reported `h3JetIndex_card._native.native_decide.ax_1_1`. This records the
observed output; it does not claim every project theorem was audited.

## Public contract boundary

`SmoothContinuationExtension` records agreement before T, terminal vorticity
balance, and terminal cascade regularity. Its fields do not explicitly promise
a Navier–Stokes solution after T.

`H3ControlProducesRealRestart` explicitly supplies S > T, velocity and pressure,
agreement before T, Navier–Stokes on (0,S), spatial C³ regularity, and third-jet
continuity at T. The checked bridge projects that stronger result to the
terminal extension package. The checked real-restart theorem retains
`EnergyClassProducesCanonicalH3Data` as its premise.

The latest quantitative neutral endpoint alternative retains all of:

- `LoggedPreterminalH3PathAdmissible`;
- `PreterminalH3EnergyClass`;
- `H3TerminalActualVorticityStrongH3EndpointPath` for the selected component;
- `H3TerminalVelocityRawFourierL2CauchyAtEndpoint`;
- a positive threshold ε.

Its conclusion remains an extension package or a terminal sequence with
bad-cone mass, a quantitative critical alternative, and higher-radial universal
escape. Printing its axiom dependencies does not discharge its hypotheses or
exclude its alternative branch. `tools/audit/Contracts.lean` is the executable
record of these types and dependencies.

## Five files outside root coverage

Exact source paths, source hashes, and actions are in
[source-coverage.json](source-coverage.json). The existing gap inventory remains
unchanged until each source is repaired or independently checked.

| Source role | Classification | Next action |
|---|---|---|
| Fourth-q forcing primitive mass aggregate | Mixed duplicated and unique results | Compare with the active Escape/Pair/Bound chain; preserve unique statements. |
| Older fourth-q derivative primitive module | Exact duplicate after its first import line; that import is missing | Convert the old file into a compatibility import of its active copy and build the old target. |
| Separated weighted PDE terms | Standalone candidate with unique results | Compile separately, then decide supported coverage. |
| Physical L² Cauchy frontier | Standalone candidate with unique results | Compile separately and preserve its physical/Fourier equivalence. |
| Strict-time vorticity decay | Standalone candidate with unique results | Compile separately, then decide supported coverage. |

An unreferenced file is not automatically obsolete. Adding all five to the root
would introduce duplicate declaration conflicts and a known missing import.
No Lean source changes are made by this documentation patch.

## Documentation repair

The source index now covers all 2,383 project modules rather than the obsolete
766-entry queue. It orders existing import edges and records source provenance;
it does not certify the five excluded files. A generated revision stamp is
informational; `--check` verifies source content and ordering, so an unrelated
Git commit does not invalidate the index.

The 22 prose fragments remain a partial exposition. The `MulRat` fragment is
explicitly mapped to `PrimeTensor/Mul/Rat.lean`; its existing labels, fragment
name, and PDF path are preserved. Source references in the prose use the current
Lean path. Previously rendered PDFs have not been regenerated and may retain
old path text. The fragment builder excludes generated `modules.tex` when
rendering individual fragments.

Run the inexpensive checks without rendering PDFs:

```bash
python3 proof/generate_index.py --check
python3 proof/check_fragment.py --all
```

Next, repair and validate the duplicate module's compatibility path. Then check
the standalone candidates and resolve the mixed aggregate before beginning the
clock/width path migration. Keep source moves separate from theorem changes.
