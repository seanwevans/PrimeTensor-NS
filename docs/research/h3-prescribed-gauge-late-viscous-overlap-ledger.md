# Two physical late PDE clocks: additive charge or forced overlap

**Base:** `eccdd0c0abb7d484151e7800e7bf5881bd51b27e` — squared terminal H3 tail budget from the secondary physical PDE clock.

## Hard mathematical issue

Both the primary and the secondary finite-band Navier–Stokes clocks have
strict positive physical time widths and pointwise full-H3 viscous floors.
Each is separately bounded by the *same* terminal viscous action

    B = integral_(m)^T D_H3(t) dt.

It is incorrect to sum their independent `<= B` bounds as if the intervals
were disjoint. The actual two-interval integral calculation proves exactly:

    eta1*A + eta2*h/2 <= B
       OR
    r < s+eta2 AND s < r+eta1.

The second alternative is strict overlap of the clock interiors. If the
sum of heights times widths is greater than B, the second alternative is
*forced*. Touching endpoints is handled in the additive case.

## Constructive physical specialization

From an actual first finite-cutoff spike

    V < P * D_low,J(r),     m < r < T,     A = V/(2P),

and a secondary clock at `sState` or `sSource`, the existing actual PDE
persistence constructions yield the heights and widths required by the
scalar integral theorem. No full-H3 dissipation continuity is assumed.

From the previously proved constructive two-slice gap

    A^2 <= R B (E+3D(sState))(E+3D(sSource)),
    4 R B E^2 < A^2,

one can choose `h=A/(12 sqrt(RB))` and obtain the secondary clock. The
overlap/additive dichotomy then has explicit secondary floor
`h/2 = A/(24 sqrt(RB))`, without assuming the clocks are separated.

## Scope

The committed squared-tail *cofinal* result has eliminated the primary
clock and no longer exposes the required pointwise primary low-band height.
Therefore the new physical conclusion is proved at the level of two
certificates, with the primary height as a stated premise. It does NOT
assert that the premise can be recovered for the same cofinal witnesses
from the squared-tail theorem's final statement alone. A future theorem
must retain the first clock and the constructive secondary witnesses
simultaneously to apply this ledger unconditionally on that cofinal family.

This is a genuine separation/overlap geometric obstruction, not a
Navier–Stokes regularity theorem. An overlap can persist; no contradiction
with finite total dissipation is claimed.

The archive contains no proof placeholders. It must be elaborated against
the project’s pinned Lean/mathlib toolchain locally.
