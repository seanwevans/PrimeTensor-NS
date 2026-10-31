# H³ Critical Radial-Energy / Annular-Geometry Refactor — Pilot 3

Base: locally verified checkpoint `6b95cba1` on `refactor/h3-critical-gradient-pilot`.

## Canonical dependency structure

1. `Critical/AnnularGeometry/EnergyOuter.lean` — physical source/energy and outer annular radius bounds.
2. `Critical/RadialMoments/SecondMomentEnergy.lean` — `m = 2` energy burden under the critical eighth-power cutoff.
3. `Critical/RadialMoments/SharpFourthEnergy.lean` — sharp fourth-power cutoff/energy burden.
4. `Critical/RadialMoments/AllOrdersSharpEnergy.lean` — arbitrary fixed radial order `m`, with exact exponent `16m+3`.
5. Existing canonical consumer `Critical/Spectral/EnergyGate.lean` — its import of the *historical* all-orders module is redirected to `Critical/RadialMoments/AllOrdersSharpEnergy` without changing a non-import line.

The four original Control paths remain forwarding compatibility imports. All statements, hypotheses, namespace declarations, and non-import proof lines of the four moved sources remain unchanged. The earlier `Critical/Spectral/EnergyGate` proof body is likewise unchanged. This does **not** derive the higher radial moment majorant, source cap, terminal clock, or cutoff hypotheses; the original theorems remain conditional.

The Pilot 3 manifest `docs/audit/critical-radial-path-map.json` records hashes of original source files, non-import proof bodies, and canonical import lists. It additionally records the prior-to-new import lists for the earlier canonical spectral consumer. The Pilot 2 manifest's `canonical_imports` entry is updated and receives an `import_refactorings` provenance record. Its original implementation body hash remains intact. Thus **both independent Pilot 2 and Pilot 3 integrity checkers** continue to pass.

## Safety and usage

The extended shared `module_migration.py` supports explicit import-only rewires of *previously migrated canonical consumers* while preserving their prior proof-body seals. Existing Pilot 1 and Pilot 2 migration configurations are unaffected. The Pilot 3 script is dry-run-first, with an explicit `--apply`. It expects HEAD `6b95cba1` by default and refuses apply if a selected old module, previous canonical consumer/manifest, baseline, or proof index has uncommitted changes. It also refuses to overwrite a canonical target.

The migration applies atomically with respect to its tracked-file snapshots and newly created files: internal exceptions restore original modules, earlier consumer, earlier manifest, baseline, and index, and remove new files and directories. It checks source inventory and generated index. `--check` independently verifies the four new proofs/shims and the previous canonical consumer rewire; the full baseline runs all three pilot integrity checkers.

Commands after extracting this pilot into the existing refactor worktree:

```bash
python3 tools/refactor/critical_gradient_pilot.py --check
python3 tools/refactor/critical_transport_pilot.py --check
python3 tools/refactor/critical_radial_pilot.py --dry-run
# When satisfied:
python3 tools/refactor/critical_radial_pilot.py --apply
python3 tools/refactor/critical_transport_pilot.py --check
python3 tools/refactor/critical_radial_pilot.py --check
python3 proof/generate_index.py --check
python3 proof/check_fragment.py --all
lake build PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Spectral.EnergyGate
bash tools/audit/baseline.sh --reuse-build
```

No Lean sources are shipped; the script reads the exact local proof implementations, preserving their existing Unicode and proof bodies. No commit, merge, or push occurs. The pinned-toolchain build and full audit must pass before making the next checkpoint.

Expected index: 3,093 project modules (if starting at 3,089), no uncovered modules, and no missing project imports.

## Synthetic verification

The migration tool was tested in temporary synthetic Git worktrees for: read-only dry run; checkpoint mismatch; uncommitted tracked-file guard; successful four-file migration; direct canonical-consumer import rewiring and prior manifest compatibility; proof-body tamper detection; prior-manifest tamper detection; and full restoration of the previous canonical consumer and manifest on an injected failure.

Synthetic checks are not Lean elaboration. Compilation must be performed in the repository's pinned Lake environment.
