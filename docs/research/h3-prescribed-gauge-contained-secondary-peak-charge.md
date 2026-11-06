# Contained secondary PDE clock: true three-piece H³ viscous payment

**GitHub base:** `5297d1094cfd2add2f06d14126f45430eaf89107` — two-sided overlap-safe PDE-clock packing.

## Mathematical distinction

The previous ledger charges the maximum of three individually safe quantities,
with the primary clock `I₁=[r,r+eta1]` and the secondary `I₂=[s,s+eta2]`,
`r<=s`. It is not sharp when the secondary interval is contained inside the
primary interval, is shorter, and has a higher dissipation floor.

Assume `s+eta2 <= r+eta1`. Three genuine nonoverlapping time portions give

* `[r,s]`: `D_H3 >= A`;
* `[s,s+eta2]`: `D_H3 >= H`;
* `[s+eta2,r+eta1]`: `D_H3 >= A`.

Thus

    eta1*A + eta2*(H-A) <= B,   B := integral_m^T D_H3.

This does not need `H>=A`, but if `H<A` the bound is weaker than the original
full-primary charge. Combine the two rigorously:

    eta1*A + eta2*max(0,H-A) <= B.

For the constructive two-slice spike the second floor equals

    H = A/(24 sqrt(R B)),  R=96 C0 (J+2)^5.

The excess `H-A` is positive only when `sqrt(R B)<1/24`; no proof in this
patch assumes that inequality. In particular the new statement remains valid
if `s=r`, when the previously charged primary prefix has length zero.

## Formal proof architecture

1. An interval-integral triple partition, using two adjacent-interval
   equalities and integral monotonicity, constructs the three actual costs.
2. An elementary maximum split chooses the positive-excess formula if
   `A <= H`, or the full-primary cost if `H <= A`.
3. A Navier–Stokes specialization uses the same primary and secondary
   finite-band clock certificates and preserves the three-way packing
   estimate at that very same selected secondary time and duration.
4. The cofinal theorem retains all existing prescribed-gauge first-crossing
   witnesses, spectral alternatives, frequency escape, original disjoint
   viscous-charge bound and terminal-tail limit; it adds the contained-peak
   payment to the active two-slice kinetic-gap alternative.

This proves no positive *uniform* excess, frequency cap, or Navier–Stokes
continuation theorem. The Lean file has no placeholders. Local Lean/mathlib
compilation is required; the source archive cannot certify elaboration.
