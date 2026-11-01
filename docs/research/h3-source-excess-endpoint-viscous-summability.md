# Summability of synchronized endpoint physical H³ viscous costs

**Base:** `4f8293a8` — same fivefold source witnesses and attained
spectral maxima as the disjoint integrated endpoint-cost selection.

## Real L¹ budget

The previous synchronized gate provides strictly separated internal
intervals `[p(k),p(k)+η(k)]` and a positive attempted threshold

    H(k) = R(k)^2 ε(k)^2 / 8.

If a strict spectral-maximizer viscous spike occurs, `η(k)>0` and
`H(k)<D₃(r)` throughout its internal interval. When no spike is present,
the interval has zero width. The new generic lemma **does not** incorrectly
assert the positive floor at the zero-width singleton; it masks the floor
to zero there before invoking disjoint interval integration.

Under the additional assumption

    IntervalIntegrable (velocityH3DissipationAt u) volume a T

the actual real dissipation integral supplies a common bound:

    Σ_{k<m} η(k) H(k) ≤ ∫_a^T D₃(r) dr.

Therefore `Summable (fun k => η(k)*H(k))` and

    η(k) R(k)^2 ε(k)^2 / 8 → 0.

The cofinal theorem selects exactly the same `t,w,v,sSource,sState`,
the quartic short widths `δ`, and the disjoint internal endpoints `p,η,N`
for which the **synchronized** source/spectral PDE-clock alternatives
have already been proved. There is no change of maximizing sequence.

If heights are eventually at least one, then `η(k)→0`; this is a
separate conditional consequence, not a uniform persistence estimate.

## What this does and does not prove

This converts the finite physical endpoint sum into actual summability,
not merely a countably infinite series of unrelated pointwise spikes.
It does **not** establish divergence of these charges or eliminate every
non-spectral alternative. The source and endpoint subinterval families
may overlap for the same k, so their budgets are each bounded by the full
time integral but are not added together. No terminal trace or global
Navier–Stokes regularity conclusion is asserted.

## Declarations

- `h3Critical_disjointInternalViscousHeights_finiteRealBudget`
- `h3Critical_scalar_endpointHeightLower_forces_widthCollapse`
- `h3Critical_noL2Trace_cofinalFivefold_endpointViscousChargeCollapse`

The dedicated audit registrar adds all three declarations to the root
and axiom audit, idempotently. The local Lean/mathlib toolchain and full
baseline build must validate this patch before committing.
