# Overlap-safe unshared-prefix payment for the cofinal prescribed-gauge dual PDE clocks

**Base:** `63f5054fdad6fdb4ac0f153477a12ef705ed02d4` — retained primary and secondary PDE clocks on the same prescribed-gauge cofinal witnesses.

The previous dual-clock theorem proves either an additive charge for disjoint full intervals or an overlap alternative. An explicit quantitative cost is recoverable even under overlap because the secondary clock starts at an original maximizer `s` in the compact interval `[r,r+(T-r)/2]`; in particular, `r <= s`.

Write `A = V/(2P)`, `B = integral_m^T D_H3`, `eta1` for the first explicit PDE-clock width and `eta2` for the second. For `h = A/(12 sqrt(R B))`, with `R = 96 (3+C_L) (J+2)^5`, the physical rate branch and its kinetic-gap hypothesis construct the second window and prove

    min eta1 (s-r) * A + eta2 * A/(24 sqrt(R B)) <= B.

Proof: let `ell = min eta1 (s-r)`. Then `[r,r+ell]` lies in the original primary floor interval and ends no later than `s`; `[s,s+eta2]` lies in the secondary floor interval. These two portions are disjoint up to a single endpoint. The already-proved exact interval-integral additive lemma gives their combined charge against one and the same physical terminal tail. The result is independent of whether the full intervals intersect.

The patch adds a generic ordered two-clock trimmed-prefix theorem, its actual Navier–Stokes specialization, a new refined late-branch proposition and a cofinal lift that keeps the identical minimal first-crossing witnesses and disjoint original viscous sums. It does not require a terminal-uniform cutoff, derivative, modulus or time-width bound.

In the degenerate limiting configuration `s=r` the primary prefix length vanishes; no artificial lower bound or Navier–Stokes continuation conclusion is claimed.

No proof placeholders. The registrar checks each theorem, the definition and their axioms. Full elaboration remains to be run with the pinned repository Lean toolchain.
