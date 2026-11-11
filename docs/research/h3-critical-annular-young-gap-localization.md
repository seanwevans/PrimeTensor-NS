# Actual critical H3 Young-gap localization on a finite frequency band

**Pinned accepted HEAD:** `ad94cc03cb1f3356ca94dafa0344313f1f9408c4`.

## Mathematical step

The previous checkpoint established the *actual* sharp real-physical low/high
Fourier projection, its Plancherel cross-orthogonality and the kinetic-only
source compensation bound. But the sharp Young remainder is weighted by
`q(ξ)^3` and involves variable anti-heat multiplier `q(ξ)`, rather than a
constant positive rate. Identifying these two mismatches is the next hard
step, not a new energy axiom.

Fix `0 <= lo <= q(ξ) <= hi` and choose
`rate=(lo+hi)/2`, `width=(hi-lo)/2`. For arbitrary complex `z,r`,

    |r-rate*z| <= |q*z-r| + width*|z|.

With nonnegative q and bounds on its third power, the sharp Young square
bound gives

    lo^3 |r-rate*z|^2
       <= 2 q^3 |q*z-r|^2 + 2 hi^3 width^2 |z|^2.

For the ACTUAL physical Navier--Stokes state, the previously established
almost-everywhere PDE Fourier identity is

    r = -q*z - f,    so q*z-r = f+2*q*z,

with `f` the full genuine solenoidal Leray forcing. The new actual-source
pointwise theorem therefore yields on the same q-band

    lo^3 |r-rate*z|^2
       <= 2 q^3 |f+2*q*z|^2 + 2 hi^3 width^2 |z|^2.

The final theorem integrates this inequality over any measurable set whose
frequencies lie in the q-band, keeping the three `IntegrableOn` obligations
visible. Thus the exact Young-gap payment and the annulus-width error remain
separate; there is no unsupported assertion of terminal-integrable source.

## Remaining problem

To feed this result into the accepted full physical highpass kinetic
compensation, one still needs to prove the three fixed-snapshot integrability
requirements automatically from the raw Fourier L2 states on a bounded
annulus, convert the integral terms into the actual sharp physical annular
L2 norm, and account for the outer-frequency tail beyond that annulus.
The factor `hi^3 * width^2` can diverge for moving bands, and no uniform
terminal bound follows from this increment alone.

## Declarations

- `thirdFullKinetic_annularAntiHeat_norm_le244`
- `thirdFullKinetic_annularAntiHeat_weightedSquare244`
- `thirdFullKinetic_midpointAnnulus_weightedSquare244`
- `thirdFullPhysical_actualAnnularYoungGap_pointwise244`
- `thirdFullPhysical_actualAnnularYoungGap_integral244`

No `sorry`, `admit`, or new axioms. Lean compilation remains to be checked
using the pinned Lean 4.34.0-rc1 environment and repository's mathlib.
