# Initial kinetic L¹ budget and one sampled initial self-correlation

Base checkpoint: `03de82ea` — identify initial physical trace from sampled kinetic self pairing.

## Reduction

The preceding sampled-kinetic/self-pairing criterion required a sequence
`τₙ → 0+` on which `E₀(τₙ) ≤ E₀(0)` eventually. This exact ceiling is
not implied by mere positive-time kinetic antitonicity and may fail at
every strict positive time even for data with the correct right limit.

This patch replaces the sampled energy ceiling by an initial-data kinetic
budget with ONE integrable defect `r`:

    E₀(t) ≤ E₀(0) + ∫₀ᵗ |r(s)| ds,   0<t<b,
    ∫₀ᵇ |r(s)| ds < ∞.

The already-proved scalar integrable-primitive limit gives
`∫₀ᵗ |r| → 0` as `t → 0+`. Since the subcritical RHS theorem already
derives `E₀(t) → ‖L‖²`, this implies `‖L‖² ≤ E₀(0) = ‖U₀‖²`.
The sole remaining scalar initial pairing condition is ONE sequence
`τₙ → 0+` such that `⟪old(τₙ),U₀⟫ → ‖U₀‖²`.

Consequently the Hilbert polarization identity forces `L=U₀`,
recovering the existing precise rates

    ‖old(t)-U₀‖ ≤ ((3+C_L)*M) * t^(1−α)/(1−α)

and

    |E₀(t)-E₀(0)| ≤ δ(t) * (2‖U₀‖+δ(t)).

## New declarations

- `h3Audit_initialIntegrableKineticBudget_rightLimitUpper`
- `h3Audit_initialStrongHilbertLimit_eq_of_integrableBudget_selfPairSequence`
- `H3AuditInitialIntegrableKineticBudgetSelfPairingTrace`
- `h3Audit_initialSubcriticalIntegrableBudgetSelfPairing_identifies_physicalAndKineticRate`

## Independent analytic obligations

The initial kinetic budget is a genuine zero-time PDE/energy-data premise,
not a consequence of the positive-time energy law. The one-vector sampled
self-correlation remains independently required, as do the subcritical
initial H³ rate and the old temporal derivative joint continuity.
The old/selected relative-energy residual and terminal actual-vorticity
H³ endpoint are not used here; neither is proved by this patch.
No unconditional Navier–Stokes global regularity statement follows.

## Audit and default build

The registration script adds the module to `PrimeTensor.lean`, and four
`#check` declarations (three with `#print axioms`) to
`tools/audit/Contracts.lean`, without deleting prior checks. All of
`lake build PrimeTensor`, `lake env lean tools/audit/Contracts.lean`,
and `lake build` remain pre-push gates.

ZIP and registration syntax validated; Lean compilation requires the
user's Rocky Linux/mathlib toolchain.
