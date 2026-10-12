# Restore the H3 audit build and close the anchored Schwartz weak-sequence bridge

Base checkpoint: `b9ac8fe7` — identify initial physical traces from anchored Schwartz momentum.

## Restore default compilation and contract verification

`PrimeTensor.lean` currently imports old H3 audit modules but stops at
`OneComponentInitialCanonicalWeakFTCAbsoluteTransfer`. Recent initial-source,
subcritical momentum, kinetic, weak-identification, and anchored Schwartz
modules were **not** in the default library import chain. The previous
`tools/audit/Contracts.lean` does not check their theorem types/axioms either.

`tools/audit/restore_initial_trace_audit.py` idempotently adds nine audit
imports to `PrimeTensor.lean` and 17 contract checks (with `#print axioms` for
the theorem declarations) to `tools/audit/Contracts.lean`.

The normal build/push workflow must now run `lake build PrimeTensor` and
`lake env lean tools/audit/Contracts.lean` before the full `lake build`,
so the audit is not silently skipped.

## New theorem chain

`OneComponentInitialAnchoredSchwartzWeakSequence.lean` adds:

- `H3AuditInitialSchwartzWeakCofinalSequence`: per-Schwartz-test positive-time
  sequences approaching zero with scalar pairings approaching the actual
  physical initial velocity.
- `h3Audit_initialAnchoredSchwartzSource_of_positiveDerivative_and_weakSequence`:
  generic bridge from integrable source, positive-time scalar derivative,
  and weak test sequence to the *initial-anchored* weak momentum integral.
- `h3Audit_initialSubcriticalEnergyRate_anchoredSchwartz_of_weakSequence`:
  applies the existing actual old velocity Schwartz derivative and
  subcritical H3 actual projected-source integrability.
- `h3Audit_initialSubcriticalWeakSequence_identifies_physicalAndKineticRate`:
  restores identified rates for the actual u(0) and kinetic E₀(0).

**Independent assumptions remain:** subcritical initial H³ energy growth;
old temporal joint-continuity; existence of the weak Schwartz initial
sequences. These are not consequences of bare positive-time H³ admissibility.
The relative-energy residual and terminal strong-H³ vorticity endpoint
remain independent. No unconditional Navier–Stokes claim is made.

## Verification

No Lean toolchain is installed in the artifact environment. The local module,
root-import, full-library build, and Contracts audit must pass before commit.

## Fix 1: compilation repairs

- Specialize the scalar weak-FTC theorem to `t` and `ht`, explicitly
  aligning the local `f` and `g` abbreviations with the anchored target.
- Close the last conjunction parenthesis in the combined physical/kinetic
  theorem statement. No theorems, assumptions or audit declarations change.
- Retain the idempotent restoration script for `PrimeTensor.lean` and
  `tools/audit/Contracts.lean`; re-run it before the build.

Lean toolchain not available in packaging environment.
