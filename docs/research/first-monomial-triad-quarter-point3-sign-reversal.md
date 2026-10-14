# Full Point3 first-monomial: sign reversal and two-sided witnesses

Base commit: `9857fdcc` — `prove signed Point3 first-monomial noncancellation for real Schwartz velocity`.

## Mathematical goal

The previous proof exhibited a real divergence-free Schwartz velocity with a
strictly negative complete physical first-monomial on `Point3`. We now prove
that reversing the velocity reverses the sign of the **entire 243-term
aggregate**, not merely a selected triad or its symbolic phase. The result
is unconditional for real Schwartz data, while incompressibility is checked
for both members of the constructed pair.

Write `M(v)` for the original, five-axis-index `Point3` first-monomial
integral including the factor two from `spatialEnergyPairing`. It contains
exactly three appearances of `v` and linear spatial derivative operators.
This module proves `M(-v) = -M(v)` via the already established exact
Schwartz-to-Point3 pairing. It therefore derives, for the *same* suitable
quarter-packet width,

- `M(v) < 0`, and
- `M(-v) > 0`.

The reversal preserves real Schwartz class and physical coordinate divergence.
The new proof is based on the actual Schwartz directional derivatives and
integrals, avoiding new Fourier normalization assumptions.

## Scope

This rules out universal cancellation, nonnegativity, or nonpositivity of the
full signed first-monomial integral on the real divergence-free Schwartz class.
It does **not** establish that either Schwartz field is a solution at a
preterminal time, nor that this monomial dominates dissipation or other
nonlinear energy terms. In particular it proves neither blowup nor global
regularity for Navier–Stokes.

Next: quantify amplitude scaling relative to the quadratic energy/dissipation
terms and identify precisely which auxiliary bounds (if any) can absorb this
sign-indefinite cubic monomial in the fully instantiated PDE energy balance.
