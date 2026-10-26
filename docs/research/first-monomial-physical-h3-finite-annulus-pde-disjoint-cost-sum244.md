# Disjoint cubic annuli: finite-sum cost and terminal L¹ obstruction

Base: `832dc282` (pairwise separated cubic H³ PDE windows, Lean CI passed).

The no-strong-physical-L²-terminal-trace branch supplies an actual physical H³
spectral path, cubic high-frequency snapshot witnesses, finite outer annuli,
strictly positive PDE-controlled persistence windows, and a strict increasing
subsequence with pairwise separated intervals. It does *not* provide a
summability or divergence conclusion by itself.

## Exact integral consequence

Let `f` be a nonnegative real function, interval-integrable on `[a,T]`, and
let the ordered, non-overlapping windows be `[τ_k,τ_k+δ_k] ⊆ [a,T]`.
If `A_k ≤ f(t)` on window `k`, then for every finite `m`:

    sum_{k<m} δ_k A_k <= sum_{k<m} integral(window_k,f)
                         <= integral(a,T,f).

Proof: the second inequality telescopes the primitive, including nonnegative
gaps, using `intervalIntegral.integral_add_adjacent_intervals` and
`intervalIntegral.integral_mono_interval`. The first follows by integrating
pointwise floors. Neither an infinite-series interchange nor a singular
endpoint limit is presumed.

For actual Navier–Stokes preterminal snapshots, the radial Fourier partition
and nonnegativity show

    D_{<Q}(t) - D_{<R}(t) <= D_full(t).

Consequently the selected cubic windows imply, conditional on the actual
full H³ dissipation being interval-integrable up to `T`, that

    forall m, sum_{k<m} δ_{v(k)}(v(k)+1)^3 / 2
              <= integral_a^T D_full(t) dt.

The last theorem constructs the selections directly from the existing
no-strong-L²-trace/cofinal-PDE-window interfaces, rather than assuming a
monotone original witness time sequence. The terminal L¹ assumption is
**explicit and additional**, as in general neither preterminal H³
regularity nor pointwise finiteness of `D_full` implies it.

## What remains

This rules out only a divergent selected sum *under terminal L¹*. No such
divergence has been proved. A sufficiently sparse selection or sufficiently
small persistence widths could have summable costs. The next mathematical
frontier is a quantitative restriction on widths/radii/source growth (or a
more efficient covering argument) strong enough to prevent summability.
