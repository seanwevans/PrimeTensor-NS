# Actual physical source envelope in the minimal quadratic-sharp clock

Base commit `24064ec4`: an attained canonical source envelope on every compact, strictly interior time interval.

## The circularity to avoid

The old exact clock first fixes a minimal first-crossing annulus at physical time `t`, then uses an *arbitrarily chosen* projected-source ceiling `C` on the half-terminal interval `[t,t+(T-t)/2]`. The coefficient `C` can be made arbitrarily large while remaining a valid ceiling, so escape of its square does not by itself mean that the actual physical projected source grows. Replacing `C` by an envelope **after** computing the clock is not justified: the exact clock width depends on `C`.

## Canonical-clock construction

Fix the minimal first-crossing `N` and initial spectral bound `K=‖G(t)‖` first. Then define

`C* = sup {‖R(s)‖_(physical L²) : t ≤ s ≤ t+(T-t)/2}`,

where `R(s)=Δu(s)-P(u·∇u)(s)` is the actual projected momentum source. The previous canonical-envelope theorem guarantees both finiteness and attainment on this fixed compact interval, and pointwise domination of the actual source by `C*`.

Use `C*` *before* defining `Λ(R,Q,K,C*)`, `Ξ(R,Q,C*)`, and

`δ = min( (T-t)/4, 1, gap/[4(Λ+1)], sqrt(gap/[4(Ξ+1)]) )`.

The already-established anchored physical PDE persistence theorem then supplies the exact quadratic-sharp annular dissipation floor on `[t,t+δ]`. No post-selection substitution of coefficients is required.

The first new theorem is a pointwise minimal-cutoff canonical-clock existence statement with an attained physical source maximizer. The second theorem transports it to every physical no-strong-terminal-`L²`-trace cubic snapshot, retaining strict-time membership, cofinal convergence, minimality of the crossing, and exact source-anchored clock coefficients.

## Remaining analytic work

This changes the **choice of witness**. The existing conditional ninth/eighth PDE barrier and source-growth arguments are proved on existential arbitrary-ceiling witnesses. Their proofs cannot be transferred to this newly constructed canonical sequence merely by identifying the two existential sequences. The next step is to rerun the disjoint-window finite-dissipation extraction and three-scale PDE barrier with this canonical sequence. Only after that transfer can a source-coefficient escape on this sequence be interpreted as growth of an actual physical projected source norm at some point of its enclosing window.

No regularity contradiction, rate-bound hypothesis, or noncompression hypothesis is asserted here.
