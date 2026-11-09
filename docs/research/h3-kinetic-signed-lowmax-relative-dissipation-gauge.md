# Native signed sixth flux: relative dissipation-density or outer frequency escape

**Pinned base:** `13f0d52f66900b0de5486dd0cc220d66058ef04d`.

## The missing mathematical distinction

The previously established signed sixth-flux kinetic PDE rate/clock fork is

`(y-x)*H <= 16*D_gap OR H^2 <= 32*(L_R+L_Q+1)*D_gap`, for an attained
finite annulus at outer radius `Q >= R`. The gauge-rate bridge upgrades this
to `(y-x)*H <=16*D_gap OR G<Q OR H^2 <=32*C_G*D_gap`, with

`C_G=2*sum_{j=0}^G L_j(E0)+1`.

Here `E0=velocityH3Energy0At u b` is the fixed *physical kinetic anchor*,
`L_j` is the existing nonnegative finite-band kinetic-only Lipschitz
coefficient, and `D_gap=integral_[x,y] velocityH3DissipationAt u r`.

The accepted energy cap provides the **positive floor**

`h=eta/[8*(thirdFullKineticSignedLowMaxPhysicalHighTailFactor244(E)+1)]>0`

whenever `0 <= velocityH3EnergyAt u t <= E`, with `h<=H` independently of
inner radius, observation time and gap index.

## Fixed-gauge limiting step

For each fixed natural G, the real rate `C_G` is finite and strictly
positive. The original disjoint kinetic windows already imply

`D_gap(k) -> 0`.

Consequently the finite scaled rate payment `32*C_G*D_gap(k)->0`. Since
`h^2>0`, the inequality `H^2<=32*C_G*D_gap(k)` is impossible for every
sufficiently late gap *with this chosen G*, whenever `H>=h`. The resulting
necessary alternative is exactly

`(y_k-x_k)*h <=16*D_gap(k) OR EXISTS Q>=R, G<Q`.

This does not divide by the potentially vanishing gap length. When
`x_k<y_k`, the first branch is precisely the positive lower bound on
average actual H3 dissipation

`D_gap(k)/(y_k-x_k) >= h/16`.

Its strict negation forces `Q>G`. All these statements are actual
physical-time and spectral estimates: no Schwartz tolerance, fictitious
uniform rate, or new Navier--Stokes hypothesis is added.

## Quantifier order and mathematical frontier

The cofinal theorem proves `for each G, eventually k, for all R,t ...`.
It deliberately does **not** prove `eventually k, for all G ...`, which
would be false without further control of the growing kinetic rate `C_G`.

The source-conditioned theorem further uses the already accepted
`tenth-power radius/energy` obstruction. If the earlier cubic baseline,
actual radial/physical-energy escape, and quadratic in-gap viscous residual
are **excluded**, its gamma-independent limit yields a genuine high-radial
carrier. Importantly, the same residual exclusion itself supplies
`velocityH3EnergyAt u t <= E`; no additional cap is silently assumed.
Thus the full signed physical adverse observation also meets the
relative-density-or-outer-gauge fork.

The result does **not** rule out the earlier residual nor prove a
vanishing *relative* dissipation density. Finite total H3 dissipation gives
`D_gap(k)->0`, not `D_gap(k)/(y_k-x_k)->0`. That ratio is the unresolved
physical time-concentration obstruction. The result also does not produce
a single cofinal threshold uniform for moving G(k).

## New declarations

- `thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244`
- `thirdFullKinetic_signedLowMax_finiteGaugeRate_pos244`
- `thirdFullKinetic_signedLowMax_relativeDensityOrGauge_scalar244`
- `thirdFullPhysical_signedLowMax_tail_relativeDensityOrGauge244`
- `thirdFullPhysical_kineticGaps_signedLowMax_tail_densityOrGauge244`
- `thirdFullPhysical_kineticGaps_signedLowMax_tail_lowDensity_forcesGauge244`
- `thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_densityOrGauge244`

The ZIP and registrar have been checked statically, including the
idempotent apply/check mechanism. Actual Lean kernel elaboration must be
run in the project's pinned Lake/mathlib environment.
