# Nonintegrable-branch disjoint H³ quarter-cubic barriers

Baseline revision `251b622c`, with exact physical source and spectral-state anchors.

The constructor `h3Path_cubicHighSnapshot_has_exactAnchorCanonicalClock244`
already proved the strict quarter-height first-crossing margin

    (n+1)^3/4 < [D_{≤N+1}(t)-D_{≤n+1}(t)] - (n+1)^3/2.

The preceding every-tail/diagonal/disjoint theorems discarded that witness
field. This module reconstructs the same physical first-crossing annulus on
every terminal subtail and exports the margin, without assuming finite total
H³ dissipation or a positive terminal kinetic-mass limit.

The same exact source-envelope maximum and quadratically sharp anchored PDE
width are retained while diagonalizing, then selecting pairwise-disjoint
physical windows. The local certified dissipation cost is

    δ(v k) (v k+1)^3/2 ≤ ∫_[t(v k),t(v k)+δ(v k)] D_annulus,k(r) dr.

The selected indices satisfy `k ≤ v k` and their inner radii diverge.
Consequently the already formalized scalar strict quarter-gap rate barrier
turns bounded positive partial sums into the three-way eventual alternative,
for every epsilon > 0:

    (v k+1)^3 (T-t(v k))/4 ≤ epsilon,

or

    (v k+1)^6 ≤ 16 epsilon (Λ_k+1),

or

    (v k+1)^9 ≤ 16 epsilon² (Ξ_k+1).

Otherwise the positive certified cubic-cost partial sums exceed every real
bound. Here Λ_k is the exact linear physical PDE variation coefficient
computed from the actual spectral norm and projected-source envelope, and
Ξ_k the exact quadratic anchored coefficient. No global terminal physical
H³ L¹ budget is invoked or concluded. This is a necessary alternative,
not a Navier–Stokes continuation or regularity proof. In particular,
nonintegrability of the full dissipation is compatible with either branch.

Lean declarations:
- `h3Critical_noL2Trace_everyTail_activeQuarterCubicPhysicalAnnulus`
- `h3Critical_noL2Trace_cofinalQuarterCubicAnnulusDiagonal`
- `h3Critical_noL2Trace_disjointQuarterCubicAnnuli_unboundedCharge_or_sixthNinth`
