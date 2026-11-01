# Calibrated cofinal source-peak persistence: quantitative width compression

Checkpoint `261b21e9` proves positive, pairwise disjoint quartic persistence
windows and a physical H³ dissipation cost. Its existential output records
`R_k^4 delta_k <= 1`, but not the actual formula choosing `R_k`. Hence no
lower bound on `delta_k` in terms of measurable source excess and PDE costs
was available from that public theorem interface alone.

## Explicit analytic calibration

At a strict physical time `t`, define the actual source excess

    P = ||H_{rho,i}(t)|| - B_{sigma,M} > 0,

with `B_{sigma,M}` the proved kinetic-anchored source barrier. On a chosen
compact positive-time window of width `w`, use the actual source ceiling C
and weighted H³ spectral-state ceiling E to set

    A = 3 + C_L(||U(t)|| + E),
    B = 12 C² + 2(D_full(t) + M),
    R = max(1,sigma) + 1 + A² B / P²,
    delta = min(w, R^-4).

The already proved physical quartic-clock displacement estimate and
radial dissipation antitonicity then show

    for every s in [t,t+delta]: D_>sigma(s) > M.

Importantly the *equalities* for R and delta are now exported in Lean,
not hidden in the proof of a weaker existential proposition. C and E are
proved to exist individually on each selected compact strict-time window
from the actual PDE representative's continuity, not assumed uniformly
as t approaches the terminal time T.

## Cofinal physical costs

Under the already explicit no-physical-L²-terminal-trace branch, the
established source-peak sequence supplies a fixed Fourier coordinate and
strictly separated windows `t(vk)` with local C_k,E_k. The new theorem
recalibrates every index by the above formulas and charges its shortened
window to the actual full physical H³ dissipation:

    sum_{k<m} M(vk) * delta_k
      <= sum_{k<m} int_{(t(vk),t(vk)+delta_k]} D_full(s) ds

in extended nonnegative integrals. No terminal-uniform bound is claimed.

## New rate-or-width alternative

For any positive physical local cost budget J on a calibrated window,

    M * min(w, R^-4) <= J

implies the exact dichotomy

    w <= J/M        OR        M/J <= R^4.

The first branch says the original geometric window was already short.
The second says the frequency radius must grow enough to compress the
quartic clock. Since the calibrated R is explicitly
`max(1,sigma)+1+A²B/P²`, the second branch identifies precisely which
source-margin / local-PDE-cost ratio must permit that growth.

This is a *necessary quantitative constraint* on any finite-dissipation
terminal scenario; neither disjunct is ruled out. There is no inference
that the weighted widths diverge or that Navier–Stokes globally extends.

## Declarations

- `h3CriticalSourcePeakCalibratedRadius` (definition)
- `h3Critical_positiveSourceMargin_explicitDominantQuarticRadius`
- `h3Critical_strictSourcePeak_explicitCalibratedQuarticPersistence`
- `h3Critical_noL2Trace_cofinalCalibratedQuarticWidths_and_fullCosts`
- `h3Critical_calibratedQuarticWidth_finiteCharge_forces_compression`
- `h3Critical_calibratedPhysicalDissipationBudget_forces_width_or_radius`

The submitted source is statically inspected but NOT compiled against Lean.
Verify with the pinned repository Lean/mathlib toolchain and full baseline.

## Lean proof correction (fix1 at `261b21e9`)

The compiler exposed a **genuine witness mismatch**, not merely a syntactic
addition-order problem. The previous construction used the cofinal theorem
which separated its already selected short quartic windows, while the new
calibrated radius can produce a different short width from the full original
window. Therefore the old separation proof did not apply. The corrected proof
selects directly from `h3Critical_noL2Trace_cofinalSourceWindows_postDropGradientGate`,
whose **full source-driven widths** are separated, derives the local physical
ceilings at each source peak, and recalibrates within each original full
window. Hence `delta <= w` now implies disjointness without a stronger
assumption. A second compiler error was the multiplicative orientation in
`div_le_iff₀`: `M <= C*R^4` is rewritten to `M <= R^4*C`. The theorem
statements and mathematical hypotheses are unchanged.
