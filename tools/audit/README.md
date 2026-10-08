# Build and contract baseline

Run from the repository root:

```bash
bash tools/audit/baseline.sh --fresh
```

This cleans and rebuilds the root package's generated outputs with the existing
locked toolchain and dependencies. It does not upgrade dependencies, remove
source files, commit, or push. Dependency caches may be reused; this is a fresh
project build, not a source rebuild of mathlib and Lean themselves.

For an already built checkout, `--reuse-build` performs the same checks without
`lake clean`. The report records which mode was used. Reports are saved under
`.lake/audit/` with distinct timestamps and process IDs, outside `.lake/build/`.
The final console line gives the exact directory. Keep that directory when
recording a baseline; it contains:

- source commit, working-tree status, per-file SHA-256 hashes, and input digest;
- toolchain, lockfile, Lake configuration, platform and version output;
- source coverage, import graph, and source-level trust-token occurrences;
- build and root elaboration logs;
- printed continuation contracts, selected theorem types, and `#print axioms`;
- an explicit exit status and result, including failure when a command fails.

Five project modules remain outside the root import closure and are listed in
`known-source-gaps.json`. All five are now explicit standalone targets. The
source inspector rejects any project module not covered by the root or those
targets. `Standalone.lean` and `Compatibility.lean` also check coexistence with
the root API. A successful baseline requires all those builds/checks to pass;
static coverage alone is not compilation evidence.

The primitive aggregate imports its 14 shared declarations and retains its six
unique declarations. The exact map is in
`docs/audit/primitive-declaration-map.json`. The final aggregate repair still
requires the accompanying Lean baseline run before it can be called validated.

A passing baseline covers every project module and the selected contract/API
checks. It does not establish that a conditional endpoint alternative has
been eliminated. Token scanning is not a Lean parser;
use the actual printed axiom dependencies when reviewing proof trust. Ordinary
Lean axioms and native-evaluation dependencies must be interpreted explicitly,
not treated as proof holes merely because they appear in this output.

`Contracts.lean` imports the existing root solely for this audit. It is not
imported back into the library. The first patch does not change CI or theorem
statements. Once the baseline has succeeded, CI evidence retention can reuse
these checks without forcing a second clean build.

The standalone roster now also includes the separated weighted PDE-terms
module. `Standalone.lean` checks its unique theorem alongside the root and
prints its axiom dependencies. Its import path and theorem statement are preserved; the theorem delegates to
the existing strict-time weighted PDE factors result. Its inclusion in the roster requests validation; only a successful
baseline run establishes that it builds with the current dependencies.

The roster also includes the physical L² Cauchy-frontier module, with its source
unchanged. `Standalone.lean` checks its eight named declarations and prints
axiom dependencies for the exact physical/Fourier defect identity, endpoint
Cauchy equivalence, and conditional radial closure. This does not assert that
the endpoint Cauchy condition follows from the other path hypotheses.

Strict-time vorticity decay is also enrolled in the standalone roster, with
both public theorems checked in `Standalone.lean`. This is decay along spatial
escape at each fixed strict preterminal time, not a uniform-in-time estimate
near the endpoint. Detailed audit output remains enabled.

The first aggregate build exposed an unavailable `MulRightStrictMono ℝ`
instance in a retained cancellation step. The repair uses the existing positive
coefficient hypothesis and `mul_le_mul_of_nonneg_left` by contradiction.
The statement and assumptions are unchanged; Lean revalidation is pending.

The clock/width migration is checked by `check_clock_paths.py` and
`ClockPaths.lean`. The first verifies preserved implementation bodies and old
forwarding paths; the second checks old/new endpoint import compatibility.
See `docs/audit/clock-path-map.json` for the complete mapping. These checks are
part of every baseline run. The original body hashes are a migration guard,
not a prohibition on separately reviewed future proof changes.

The first documented Geometry refactoring adds `H3TerminalIntervalLimits` and
its conjunction equivalence/common-subsequence transport in `IntervalLimits`.
`ClockPaths.lean` checks the new API and key axiom reports. For that one migrated
module, the manifest retains the original hash and an explicit refactoring
record; the checker requires its base revision and explanation before using
the new hash. It does not silently reset the original migration record.
