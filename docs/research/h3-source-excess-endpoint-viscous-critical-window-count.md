# Finite physical H³ budget bounds the number of critical persistence windows

**Base:** `de634dd4` — force inverse-height collapse of cofinal H³ endpoint persistence.

The previous theorem proved an eventually strict inverse-height upper bound.
This module adds a quantitative **budget packing bound**: if the same original
cofinal endpoint windows carry nonnegative charges

    C(k) = η(k) H(k),       H(k) = R(k)^2 ε(k)^2 / 8 > 0,

and every finite partial sum of charges is bounded by the finite physical
H³ dissipation integral `D = ∫_a^T velocityH3DissipationAt u`, then for any
positive fixed `γ` and every natural `m`,

    γ × #{k < m : η(k) ≥ γ / H(k)} ≤ D.

Thus at most `D / γ` windows (in counting-measure terms) can carry critical
inverse-height scale persistently; this is a bound on the **entire cofinal
selection**, not just an eventual asymptotic statement. Each endpoint spike
is charged to its own strictly separated internal interval. The original
source intervals may overlap these, so they are never additionally charged
into this same estimate.

The original non-spectral, PDE-clock, anchor-dissipation and endpoint spectral
branches remain precisely the same for the SAME cofinal witnesses.

## Precise limitations

- The budget requires an explicit terminal `IntervalIntegrable` hypothesis.
- This counts selected persistence intervals, not arbitrary independent spikes.
- It does not imply a uniform lower persistence width, elimination of the
  remaining non-spectral / PDE branches, a terminal L² trace, or global
  Navier–Stokes regularity.

## Registered Lean theorems

- `h3Critical_scalar_finiteBudget_boundsExpensiveIndexCount`
- `h3Critical_scalar_finiteBudget_boundsInverseHeightWindowCount`
- `h3Critical_noL2Trace_cofinalFivefold_boundedCriticalWindowCount`
