# Intermittent kinetic H3 rate escape and exact terminal-clock compression

**Base:** `431c8f1bd57d7c84c4cc4f8a511fbd08d060cf45`.

The accepted cofinal physical H3 annular windows have exactly selected
positive PDE widths `delta(k)`, actual finite natural outer cutoffs `N(k)`,
height profile `M(k)>0` chosen above any prescribed kinetic eighth-power
gauge, pairwise disjoint time supports and global extended physical viscous
charges. An independently finite global extended dissipation budget makes
`delta(v(k))*M(v(k))/4` summable, and therefore tending to zero.

## 1. Arbitrarily late noncompressed windows: no eventuality needed

The previous rigidity theorem demanded that a height-weighted remaining
clock satisfy `eta <= (T-x(k))*M(k)` for *all sufficiently large* k.
This is too restrictive for intermittent concentration. Replace it by:

    for every k0, there exists k>=k0
      with eta <= (T-x(k))*M(k), eta>0.

The same small-charge fork, evaluated at those recurrent indices, gives

    for EVERY K>=0 and EVERY k0,
      exists k>=k0 with K*M(k)^2 <= Lambda(k)+1.

There is no claim that the normalized rate stays large at every late index:
only an arbitrarily late sequence of large-rate events is necessary. This
correctly handles alternating compressed and uncompressed windows.

## 2. Eventual normalized rate cap forces whole-clock collapse

For the same exact kinetic PDE-selected clocks, assume additionally

    eventually Lambda(k)+1 <= K*M(k)^2    for some finite K>=0.

Then the *entire* height-weighted terminal clock satisfies

    (T-x(k))*M(k) -> 0.

The proof fixes an arbitrary epsilon>0, selects a small charge threshold
`B = min(epsilon/32, 1/(64*(K+1)))`, and excludes the PDE-rate arm of the
exact-width fork because it would imply

    M(k)^2 <= 32*K*B*M(k)^2 < M(k)^2.

Thus the clock arm must occur at all sufficiently late indices. No rate-cap
conclusion is inferred from the kinetic PDE alone; that hypothesis remains
an independent analytic obligation.

## 3. Real physical cofinal transport

The final theorem reuses
`thirdFullPhysical_noH3Trace_gaugeFiniteBudget_rateRigidity244`, retaining
*the same* physical `tau(v(k))`, `N(v(k))`, `delta(v(k))`, the prescribed
frequency gauge escape `G(v(k))<N(v(k))`, the exact annular certificate,
and summable/vanishing disjoint physical viscous charges. Both sharper
intermittent statements are proved for the actual
`thirdFullPhysicalKineticLowBandDissipationRate244` with the kinetic anchor
`velocityH3Energy0At u b`.

This theorem assumes failure of strong terminal **H3** trace plus a finite
extended physical full-H3 dissipation budget, not failure of physical L2
trace. It is a conditional necessary concentration law, not a solution to
Navier--Stokes global regularity. Missing: an independent physical PDE
upper bound for the moving kinetic rate, or a proof of noncompression.

## Audit declarations

- `thirdFull_scalar_recurrentKineticClock_forces_cofinalRateEscape244`
- `thirdFull_scalar_boundedKineticRate_forces_terminalClockCollapse244`
- `thirdFullPhysical_noH3Trace_gaugeFiniteBudget_intermittentRateDichotomy244`

Lean elaboration requires the repository's pinned Lean/mathlib toolchain.
