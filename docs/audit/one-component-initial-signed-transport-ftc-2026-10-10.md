# Initial H³ FTC: replace a full derivative ceiling by signed transport

Parent commit: `6ae8d845` — derive initial physical FTC identities from actual temporal derivatives.

## Change

The previous differentiated physical FTC criterion required
`velocityH3FormalDerivativeAt u s ≤ Cenergy` throughout each initial
interval. That is not a natural primitive PDE estimate because the viscous
term is nonpositive and may grow in magnitude at initial time.

The existing **exact Navier–Stokes** energy identity provides

`deriv (velocityH3EnergyAt u) s + 2 * velocityH3DissipationAt u s = - velocityH3TransportDerivativeAt u s`.

For each genuine `PreterminalH3EnergyClass` covering a positive initial time,
previously closed orderwise differentiability identifies `deriv E =
velocityH3FormalDerivativeAt`. Nonnegative dissipation then gives

`velocityH3FormalDerivativeAt u s ≤ - velocityH3TransportDerivativeAt u s`.

Thus a bound on the signed nonlinear transport controls the **upper** energy
growth rate without controlling the magnitude of the full derivative.
The artificial `s=0` endpoint value appearing in the prior pointwise `Icc`
contract is absorbed by a maximum; it does not assert an initial-time PDE
balance.

## Remaining explicitly assumed obligations

1. Actual initial H³ velocity integrability, measurability, Fourier compatibility.
2. Anchored physical zeroth-jet `L²` continuity on initial closed intervals.
3. Strong physical `L²` temporal derivatives, source interval integrability and a.e. bounded source.
4. Canonical H³ energy continuity at the initial endpoint and interval integrability of its formal time derivative.
5. A positive-time `PreterminalH3EnergyClass` covering every `0<s<T`.
6. A uniform upper bound on `-velocityH3TransportDerivativeAt u s` on `(0,T)`.

The last two hypotheses are **not** automatic consequences of open-time path
admissibility in this theorem. The strong terminal vorticity endpoint remains
independent and explicitly assumed for the full-time Sobolev corollary.

No new axioms, sorry, or admit.
