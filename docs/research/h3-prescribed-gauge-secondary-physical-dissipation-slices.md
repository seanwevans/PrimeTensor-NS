# Actual secondary H³ dissipation slices behind the normalized primary PDE barrier

**Base:** `82b36949fda946ebd638559c02304b74edf44242`.

## Physical step, not another algebraic normalization

The existing cofinal normalized deep-excess ledger retains the *same* selected
second cutoff `J₂`, attained spectral-state observation `zState`, and actual
projected-momentum-source observation `zSource`. Set

- `A = V/(2P)` (primary constructed floor),
- `B = ∫[m,T] D_H3`,
- `R = 96 C₀ (J+2)^5`,
- `C₀ = 3 + h3AuditInitialLerayEnergyCoefficient`,
- `E_b = 1 + 6 velocityH3Energy0At(u,b)`,
- `S₂ = (J₂+2)^5`,
- `D_s = velocityH3DissipationAt(u,zState)`,
- `D_c = velocityH3DissipationAt(u,zSource)`.

On the previously proved activated two-slice rate, kinetic gap, and
`48 sqrt(R B) <= 1`, one of the following must hold:

    (T-s) A <= 192 B sqrt(R B),

or

    A² <= 576 R B² [96 C₀ (E_b+3D_s) (E_b+3D_c) S₂ + 4].

This is an actual physical PDE constraint: from the existing
`thirdFullPhysical_lateQuinticProduct_twoActualViscousSlices244`,

    96 K₂ C₂ S₂ <= 96 (E_b + 3D_s) C₀ (E_b + 3D_c) S₂.

The proof uses that earlier physical Navier–Stokes estimate directly. Its
witness times remain inside `(b,T)`, proved from the retained exact cofinal
clock geometry. No new observation times are selected.

## Quantitative forced spike

For any real `M`, if both

    (T-s) A > 192 B sqrt(R B)
    A² > 576 R B² [96 C₀ (E_b+3M)² S₂ + 4]

then either `D_s > M` or `D_c > M`. The bound has *no hidden global cutoff
assumption*: it keeps the actual moving `S₂`. This consequence is proved as
a scalar theorem which applies to the physically resolved cofinal ledger.

## Remaining hard mathematical issue

A finite integral `∫ D_H3 < ∞` is compatible with arbitrarily high
pointwise dissipation spikes of vanishing width. The above theorem does not
bound the cutoff, produce a quantitative persistence width at `zState` or
`zSource`, or show these selected late observations belong to the original
disjoint charging intervals. The next research task is to transport the
pointwise spikes through a *genuine* physical PDE persistence estimate that
charges positive-length (preferably disjoint) portions of the viscous tail.
Do not add or double-count overlapping clock charges. This chain does not
claim global Navier–Stokes regularity.

The pinned user Lean 4.34.0-rc1 + mathlib toolchain must compile this new
module and its audit; the generating environment here has no Lean binary.
