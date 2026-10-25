# Cubic high-radial physical H³ dissipation: integrated windows

**Base commit:** `e3b991da` — localize time averaged physical H3 dissipation above fixed Fourier radii.

## Previously established

- The physical no-strong-kinetic-L²-trace alternative, retaining positive canonical terminal kinetic mass, has a **single** strict terminal sequence `τ(n) → T` and a physical high-frequency dissipation lower bound
  `D_high(n+1, τ(n)) > (n+1)^3`.
- Physical high and low frequency dissipation satisfy the exact equality `D_low(ρ,t) + D_high(ρ,t) = D_full(t)`.
- A positive-time kinetic continuity statement is available, but this does not give continuity of full H³ dissipation: the latter contains the fourth-order spatial derivative square mass.

## Theorem

Assume that the physical full H³ dissipation and the actual low-radial physical dissipation at each cutoff `n+1` are continuous on `(a,T)`. The exact partition makes high-radial physical dissipation continuous. At each `τ(n)`, select a small positive **right-hand** width `δ(n)` such that `τ(n)+δ(n)<T`, with

`D_high(n+1,s) > (n+1)^3 / 2`

on all `s ∈ [τ(n), τ(n)+δ(n)]`. Continuity supplies interval integrability. Hence the integrated cost satisfies

`δ(n) * ((n+1)^3 / 2) ≤ ∫_{τ(n)}^{τ(n)+δ(n)} D_high(n+1,s) ds`.

This uses no independent time-selection and no extra interval-integrability assumption. The widths depend on `n`; neither their minimum nor a quantitative scale is supplied. The theorem is therefore not a proof of terminal integrated divergence, a blowup exclusion, or a new unconditional smooth-continuation criterion.

## Analytic frontier

1. Discharge continuity of *bounded-radial* H³ dissipation using the repository's strong continuity of the actual weighted spectral state and bounded cutoff-multiplier control.
2. Address full H³ dissipation via parabolic smoothing or a lower-semicontinuity argument; strong H³ state continuity alone does **not** imply H⁴ dissipation continuity.
3. Establish a quantitative persistence width or a temporal coercive inequality strong enough to turn `δ(n) (n+1)^3` into a nontrivial accumulated terminal constraint.
