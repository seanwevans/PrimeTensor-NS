# First structural pilot: critical H3 physical-gradient chain

Scope: `PrimeTensor-NS` inspected at GitHub master `6fd6004a` (2026-10-30).
The local checkout may differ, so the script uses local source files and local HEAD at execution time.

## Audit findings

- The GitHub tree contains 3,082 Lean source files under `PrimeTensor/`, of which 1,608 are below `Fluid/Vorticity/Continuation/H3/`; 567 are in its `Control/` subtree and 746 in `Terminal/`.
- Source paths reach 1,007 characters, with 305 longer than 255 characters.
- The repository already maintains a 23-module compatibility-shim migration in `docs/audit/clock-path-map.json`, checked by `tools/audit/check_clock_paths.py`.
- `tools/audit/inspect_source.py` enforces root/standalone coverage and checks `known-source-gaps.json`; `proof/generate_index.py` rewrites a digest-checked topological source inventory; the baseline enforces both.
- The four pilot implementation files form a consecutive proof chain, but each lives under a historic filename encoding nearly the entire previous proof route.

## Canonical module layout

| Logical step | New implementation module |
| --- | --- |
| Annular radius to signed logarithmic transport | `PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.LogRateBarrier` |
| Exact PDE gradient/energy comparison | `PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.RiccatiBarrier` |
| Viscosity-inclusive C1 gradient charge | `PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.PhysicalGradient.ViscousBudget` |
| Real first-spatial-velocity-derivative spikes | `PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.PhysicalGradient.ActualSpike` |

The four old paths are left intact as forwarding compatibility imports. Canonical proofs import other canonical modules rather than legacy wrappers. All non-import proof text, declaration names, namespaces, and the old root/audit imports are preserved mechanically. The migration records implementation-body SHA-256 values, records canonical import lists, and adds its own static validation to the existing baseline. The final Lean build remains the required semantic check.

## Usage

`python3 tools/refactor/critical_gradient_pilot.py --dry-run` (default, no mutation)

`python3 tools/refactor/critical_gradient_pilot.py --apply` (explicit mutation)

`python3 tools/refactor/critical_gradient_pilot.py --check` (non-mutating migration guard after apply)

`--apply` refuses modified source files, baseline script, or source index. It refuses an existing uncovered module unless `--allow-existing-uncovered` is supplied; this switch does not make an uncovered module valid. A failed internal check rolls back the changed files. No Git commit or push is performed.

After applying, build the new actual-spike module and run `bash tools/audit/baseline.sh --reuse-build` before committing. A successful static check alone does not demonstrate Lean compilation.

The first pilot does not merge proofs, remove historical paths, alter `PrimeTensor.Depth`, rework the algebra-to-log-space bridge, or attempt to resolve the remaining higher-moment and clock hypotheses. After this bounded pilot passes, the same manifest/check pattern can be extended to additional critical annulus and source components.
