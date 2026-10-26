# Pairwise-separated cofinal cubic physical-PDE windows

Base: `d3e63b1f` (`extract cofinal cubic H3 annulus windows with actual projected PDE budgets`).

## The non-overlap problem

The established cofinal cubic witnesses carry windows `I_n=[τ_n,τ_n+δ_n]` with
`δ_n>0`, `τ_n+δ_n<T`, and `τ_n→T`. Their integrals are individually bounded
below by `δ_n (n+1)^3 / 2`, but the windows need not be disjoint. Summing those
individual costs as if the intervals were separate would double-count time.

## Separation theorem

For each `n`, the strict endpoint inequality `τ_n+δ_n<T` and convergence
`τ_m→T` imply the existence of `m>n` with `τ_m>τ_n+δ_n`.
Use a classical choice of such successors and recurse to define a strictly
increasing `v : ℕ→ℕ`. Then for every `k<l`,

`τ_(v k)+δ_(v k) < τ_(v l)`.

In particular, the closed selected windows are pairwise disjoint, and the
selected start times still converge to `T`. Their original outer radii,
actual projected source ceilings, initial weighted spectral bounds, polynomial
width budgets, pointwise cubic floors and integrated lower bounds are retained
without change.

## Frontier: summation and terminal integrability

The extracted non-overlapping windows allow a future finite-sum inequality
against the actual nonnegative H³ dissipation on their union. No summation or
terminal divergence is claimed in this file. Divergence would additionally
require control on `Σ_k δ_(v k) (v k+1)^3`; even pairwise disjointness alone
cannot prevent all these costs from being summable. Any attempt to infer a
regularity contradiction must first establish that quantitative lower bound.
