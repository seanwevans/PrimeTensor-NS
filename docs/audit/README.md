# Consolidation checkpoint

## Current status (base: 0bb4d596)

User-confirmed local baselines have completed the source-coverage repairs,
23-module clock/width path migration, and two limit-bundle refactorings:

| Work | Confirmed commit |
|---|---|
| Reproducible build and contract baseline | `1c4104d6` |
| Documentation source index | `8a0ecdb7` |
| Historical primitive compatibility import | `0a9ce644` |
| Weighted PDE-terms standalone repair | `4b8360c7` |
| Physical L² Cauchy-frontier standalone coverage | `e6e3b9fd` |
| Strict-time decay standalone coverage | `e091312a` |
| Primitive aggregate repair and full source coverage | `70895056` |
| Short clock/width paths with compatibility imports | `262b2e70` |
| Interval-limit bundle | `570777b1` |
| Forward-width limit bundle | `80b1aea3` |
| Full audit CI integration (local baseline) | `0bb4d596` |

The current inventory is 2,407 project modules: 2,402 reachable from the root
and five covered through standalone targets, with no uncovered modules or
missing project imports. These counts describe the current source graph;
the commits above record the user's successful local validation workflow.

Commit `0bb4d596` makes the same baseline a CI requirement for pull requests and
both Linux binary builds. It reuses the initial build, then checks all standalone
targets, compatibility imports, selected API/contracts and axiom reports,
clock-path snapshots, the source index, and the 22 prose fragments. Audit reports
are uploaded for 14 days even when the audit fails. A failure blocks packaging
and the dependent rolling release. If the initial root build fails before the
audit starts, the existing Actions build log remains the evidence; the upload
step warns when no audit report exists.

This completes the first bounded consolidation pilot once CI itself passes.
Remaining work is separate: review the printed mathematical assumptions and
trust dependencies, and choose further path migrations only where they improve
navigation. The deeper dependency chain and remaining endpoint alternative are
unchanged. The historical sections below record the state at each patch's
preparation; earlier “pending” statements are superseded by the table above.

## Historical baseline and implementation notes

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
[source-coverage.json](source-coverage.json). Five files remain outside the root import closure. The historical primitive
copy now forwards to its active canonical implementation and is explicitly
built by the baseline. The weighted PDE-terms wrapper passed in `4b8360c7`. The physical L²
Cauchy-frontier module passed in `e6e3b9fd`. Strict-time decay passed in
`e091312a`; the repaired primitive aggregate is enrolled for final validation. The compatibility checks passed in the
user-reported `0a9ce644` baseline.

| Source role | Classification | Next action |
|---|---|---|
| Fourth-q forcing primitive mass aggregate | Shared declarations imported; six unique declarations retained | Build the aggregate and check every original name alongside the root. |
| Older fourth-q derivative primitive module | Compatibility import of the active canonical implementation | Baseline builds the old target and checks coexistence with the root API. |
| Separated weighted PDE terms | Statement-preserving wrapper enrolled as a standalone build target | Build independently and check its theorem/axioms alongside the root. |
| Physical L² Cauchy frontier | Unchanged source enrolled for standalone validation | Build independently; check the physical/Fourier identity, equivalence, and conditional closure. |
| Strict-time vorticity decay | Unchanged source enrolled for standalone validation | Build independently and check both public theorems and axiom dependencies. |

An unreferenced file is not automatically obsolete. These five modules retain
explicit standalone coverage; the repaired aggregate no longer redeclares the
shared names.
The compatibility repair changes only the old duplicate implementation; the
canonical theorem bodies and statements are unchanged.

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

Next, run the baseline for the repaired primitive aggregate before beginning the
clock/width path migration. Keep source moves separate from theorem changes.

The separated weighted PDE theorem supplies L² representatives of the diffusion
and forcing terms at a strict time, under the existing H³ path and energy-class
hypotheses. This is a representation/integrability result, not a terminal bound.
Its original duplicate proof failed on stale slab arguments and rewriting.
The retained statement now delegates to the already covered strict-time
weighted PDE factors theorem while standalone coverage is checked. The weighted PDE repair passed the user-supplied baseline at `4b8360c7`.

The physical L² Cauchy-frontier module identifies the raw Fourier square defect
with the sum of three physical velocity L² distance squares. Its equivalence
reformulates the retained endpoint Cauchy hypothesis; it does not establish
that hypothesis unconditionally. The subsequent radial closure still assumes
nonextension, energy-class regularity, a selected strong vorticity endpoint,
physical L² Cauchy control, and a positive threshold. Its unchanged proofs passed the user-supplied baseline in `e6e3b9fd`.

The strict-time decay proof applies the established complementary-gradient
spatial decay to a curl pair and its swapped pair, then takes their difference.
Its second theorem gives the three-coordinate vorticity formulation. Neither
statement exchanges a spatial limit with the terminal-time limit or claims a
uniform terminal decay rate. Both are enrolled unchanged for standalone build
validation; compilation is still pending for this step.

## Final source-coverage repair (base: e091312a)

Strict-time decay passed at `e091312a`. The remaining primitive aggregate now
imports 14 shared declarations from the active Escape/Pair/Bound chain and
retains its six unique theorem/definition statements. Its size falls from 1,465 to
868 lines. `primitive-declaration-map.json` records all original names and
where each is supplied; the audit checks those names alongside the root API.

All five modules outside the root closure are now explicit standalone targets.
The inspector fails if any project module lacks root/standalone coverage. A
successful baseline will establish full project-source compilation coverage;
the final aggregate build is pending until that run succeeds. This does not
turn conditional mathematical conclusions into unconditional ones.

After this baseline passes, the next step is the bounded clock/width path
migration, retaining compatibility imports and existing theorem statements.

The first aggregate build exposed an unavailable `MulRightStrictMono ℝ`
instance in a retained cancellation step. The repair uses the existing positive
coefficient hypothesis and `mul_le_mul_of_nonneg_left` by contradiction.
The statement and assumptions are unchanged; Lean revalidation is pending.

## Clock/width path pilot (base: 70895056)

The user confirmed the full-source baseline at `70895056`. This pilot moves
23 implementations into sibling modules under
`PrimeTensor/Fluid/Vorticity/Continuation/H3/Terminal/Clock/`.
The current public endpoint is `Clock/Endpoint.lean`. The old 23 paths remain
compatibility imports; theorem namespaces, statements, and proof text remain
unchanged. Imports between migrated implementations use the new canonical paths.
`clock-path-map.json` records every old/new path and the original body hash.

Run `python3 tools/audit/check_clock_paths.py` to check that only import lines
changed, that old shims forward correctly, and that new paths satisfy the pilot
budget. The baseline runs this automatically, rebuilds old paths via the root,
and elaborates `ClockPaths.lean` with the new endpoint plus historical imports.
Lean validation of this migration is pending that baseline run.

This preserves dependency structure. It does not claim a shorter dependency
chain, faster builds, or stronger mathematics. There are now 2,406 project
modules because the old 23 paths remain available as wrappers.
The body-hash guard deliberately freezes this mechanical migration; when later
proof refactoring is explicitly reviewed, update or retire the affected guard
with an explanation rather than silently refreshing its hashes.

## First witness consolidation (base: 262b2e70)

The user confirmed the 23-module path migration at `262b2e70`. The next bounded
refactoring introduces `Clock/IntervalLimits.lean`: four named limit fields
for one fixed triple of sequences, an equivalence with the old conjunction,
and a common-subsequence transport theorem. The existing Geometry theorem
keeps its statement and delegates to the named bundle; the radial geometry
proof uses the bundle's named fields on its original selected subsequence.
No new subsequence is selected, no order assumptions are added, and the
existing radial witness definitions and public theorem signatures are retained.

The original migration body hash remains in `clock-path-map.json`. Its Geometry
entry now additionally records this refactoring's base revision, reason, and
new body hash; the checker validates that explicit snapshot. Other migrated
bodies remain frozen at their original hashes. This is the first small witness
refactoring, not completion of the larger package consolidation. Lean build,
compatibility, equivalence, and axiom checks are pending the next baseline run.

## Forward-width bundle (base: 570777b1)

The interval-limit bundle passed the user's baseline and was committed at
`570777b1`. The next bounded refactoring stays in `Clock/ForwardWidth.lean`:
`H3TerminalForwardWidthLimits` names the four rebased limits, and an equivalence
retains the exact content of their original conjunction. The new
`H3TerminalIntervalLimits.toForwardWidth` converts all four limits together
using the existing scalar rebasing theorem and the original nonzero-denominator
and sample-clock hypotheses.

The radial witness proof calls this conversion on its already selected
subsequence. Its statement, the witness definition, the floor estimate, and
all other existing declarations in ForwardWidth are preserved. No new module,
import, subsequence selection, or endpoint assumption is introduced. The path
manifest records the ForwardWidth refactoring separately from the earlier
Geometry refactoring, retaining both original migration hashes. The baseline
checks the new equivalence and conversion axioms as well as the old radial
witness theorem. Local static checks pass; Lean validation awaits the user's
baseline run.

## Kernel-checked jet cardinality (base: 0bb4d596)

The local audit passed at `0bb4d596`; this does not itself establish the result
of the subsequent GitHub Actions run. The next small trust cleanup replaces
`native_decide` in `h3JetIndex_card` with `norm_num` over the five existing jet
index abbreviations. The cardinality is the sum of the component/direction
products, 3 + 9 + 27 + 81 = 120. Its theorem statement and index types are
unchanged. No other Lean proof is modified.

The initial baseline recorded a native-evaluation axiom for this theorem.
`Contracts.lean` continues to print its transitive axiom dependencies so the
next successful Lean baseline can verify removal of that dependency. Static
source scanning alone does not verify the new proof. Because the state module
is upstream of the continuation development, changing this one proof may
rebuild many dependent modules even with `--reuse-build`.
