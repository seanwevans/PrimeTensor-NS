# Retained cofinal prescribed-gauge primary/secondary physical PDE clocks

**Base:** `e643c9216ecc391c54559b18b1f1ebac4185464b` — committed overlap-aware ledger.

## Hard mathematical issue

The existing `lateExplicitPDEClock244` cofinal theorem retained the original
strict physical first-crossing time `r`, capture radius `J`, two attained
maximizing times, and primary time width `eta1`, but its succeeding rate
and reciprocal-square-root statements eliminated the primary interval.
Hence an additive charge for the two physical intervals could not be read
from the cofinal theorem even though both earlier mechanisms were formalized.

## New cofinal transfer

Start with the **same** prescribed-gauge `U, tau, N, K, C, delta, v` from the
already-committed explicit PDE clock. Its four alternatives remain unchanged:
initial Fourier carrier, early source, kinetic clock, or late physical
viscosity. In the last case the exact primary width `eta1` and its real
pointwise dissipation floor `A=H(vk)^4/(2P)` are retained.

Write `B=integral_m^T D_H3`, `E0=1+6 E_0(b)`, `C0=3+C_L`, and
`R=96 C0 (J+2)^5`. The original clock and exact fifth-order PDE coefficient
give the following, still on the **same** first-crossing witnesses:

1. `(T-r)*A <= 4*B`; or
2. `A^2 <= 4*B`; or
3. `A^2 <= R*(E0+3 D_H3(sState))*(E0+3 D_H3(sSource))*B`.

In branch 3, whenever the explicit kinetic gap
`4*R*B*E0^2 < A^2` holds, the actual second source/state observation
forces a secondary PDE clock, with height `A/(24 sqrt(R B))` and width `eta2`.
The proof now applies the physical interval ledger directly to the
**retained primary floor** (rather than reconstructing an unseen peak):

    eta1*A + eta2*A/(24 sqrt(R B)) <= B
         OR (r < s+eta2 AND s < r+eta1).

No disjointness is postulated. The second clause states strict overlap in
the actual physical time coordinate. The original finite disjoint viscous
sum and terminal tail convergence remain part of the cofinal theorem.

## Remaining obstruction

Overlapping intervals can be paid by the same physical dissipation, so
neither second-window charge implies a contradiction from `B -> 0` alone.
A new separation estimate, overlap-multiplicity bound, or a PDE-controlled
common width/peak transfer is still required. The frequency cutoff and
attained source/state rate multipliers remain unbounded a priori.

No `sorry`/`admit` was introduced. Registrar checks definitions/theorems and
axioms; local Lean elaboration/build is required in the pinned toolchain.
