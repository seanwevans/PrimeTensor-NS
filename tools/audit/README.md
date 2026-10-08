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

The source inventory deliberately records five known modules outside the root
import closure at the original `fea879ee` checkpoint. The missing import in the historical
primitive module is repaired by forwarding to its active canonical copy.
`standalone-targets.txt` makes the baseline build that old path explicitly;
`Compatibility.lean` checks its public API alongside the root import.
`known-source-gaps.json` is a temporary explicit inventory, not a certification
or an instruction to delete these modules. Changes to either list fail the
check until reviewed. Their classification and repair order are recorded in
`docs/audit/source-coverage.json` and `docs/audit/README.md`; the other four candidates remain
pending until their individual validation steps succeed.

A passing baseline covers the default Lake targets, explicit standalone
targets, compatibility API checks, and selected contract checks. It does not claim all source files compile or that any conditional
endpoint alternative has been eliminated. Token scanning is not a Lean parser;
use the actual printed axiom dependencies when reviewing proof trust. Ordinary
Lean axioms and native-evaluation dependencies must be interpreted explicitly,
not treated as proof holes merely because they appear in this output.

`Contracts.lean` imports the existing root solely for this audit. It is not
imported back into the library. The first patch does not change CI or theorem
statements. Once the baseline has succeeded, CI evidence retention can reuse
these checks without forcing a second clean build.
