# Fixed initial-velocity self-pairing and kinetic ceiling audit

Base commit: `4daacec9` — quantify initial physical mismatch and reduce weak trace to one defect direction.

## Mathematics

Previously, a single weak sequence tested in the adaptively chosen
unknown direction `L − U₀` sufficed to identify the right limit.

This new module isolates an alternative using the **known physical initial
velocity** `U₀` and the actual kinetic energy:

1. Eventually near zero, `velocityH3Energy0At u t ≤ velocityH3Energy0At u 0`.
2. The ONE scalar test `inner ℝ (physicalOld(t)) U₀` tends to `‖U₀‖²`.

Since the earlier subcritical projected RHS and temporal joint-continuity
prove strong right convergence to `L`, the exact kinetic identity gives
`‖L‖² ≤ ‖U₀‖²`; continuity of `inner` gives
`inner ℝ L U₀ = ‖U₀‖²`. Polarization yields `L = U₀`.

The generic Hilbert bound also quantifies approximate violations:

    ‖L−U₀‖² ≤ e + 2*c

when `‖L‖² ≤ ‖U₀‖²+e` and
`‖U₀‖² ≤ inner ℝ L U₀ + c`.

The physical theorem then transfers the same exact momentum and kinetic
Hölder-type convergence estimates to the actual physical initial data,
without assuming an unknown defect-direction probe or all-Hilbert weak
traces.

## Public declarations

- `h3Audit_initialHilbert_energyCorrelation_defectBudget`
- `h3Audit_initialHilbert_identify_of_kineticCeiling_and_selfPairing`
- `H3AuditInitialKineticCeilingSelfPairingTrace`
- `h3Audit_initialSubcriticalSelfPairing_identifies_physicalAndKineticRate`

## Remaining independent obligations

The near-zero kinetic upper bound is **not** proved by open-time
Navier–Stokes H³ admissibility. Nor is the one-vector initial
self-correlation. The subcritical H³ growth rate, old-temporal
joint-continuity, old/selected relative-energy residual, and terminal
actual-vorticity strong-H³ endpoint remain separate wherever relevant.

This is a conditional trace theorem, not a proof of unconditional
Navier–Stokes global regularity.

## Integration

Run `tools/audit/register_initial_kinetic_self_pairing_audit.py` to append
the import to `PrimeTensor.lean` and four public declaration checks
(with axiom checks on the three theorems). Then build root and run the
full `tools/audit/Contracts.lean` proof dependency audit.

No Lean toolchain in this artifact environment; must compile on user's
Rocky Linux system.
