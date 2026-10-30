# Canonical higher-radial budget: unbounded normalized physical signed H³ transport

Base checkpoint `4000e4e7` — unbounded raw signed H³ transport margin on every terminal tail.

The previously committed canonical theorem proves cofinal `t_k → T` with physical `E₃(t_k) → +∞` under explicit **conditional** premises: an interval-integrable real majorant of the physical `q^(4+m)` radial moment, eventual bounded attained projected source, critical eighth-power outer cutoff, a noncompressed `(2m+3)`-weighted terminal gap, and sufficiently small positive epsilon. None of these extra bounds follows merely from finite H³ dissipation.

A general scalar mean-value argument for **log E** is stronger than the earlier raw-energy secant argument. Since `E(s)>0` on the strict tail, the exact logarithmic derivative exists and `log(E(t_k))→+∞`. For every `b∈(a,T)` and every `M≥0`, a high enough logarithmic secant must have slope exceeding `M`, so some `s∈(b,T)` has

    (log E₃)'(s) = E₃'(s)/E₃(s) > M.

The already formalized exact physical Navier–Stokes signed energy balance

    E₃'(s) + 2 D₃(s) = -Transport₃(s)

therefore yields the quantitative inequality

    -Transport₃(s) > 2 D₃(s) + M * E₃(s),

and equivalently `h3PathFullDissipationTransportExcessRate u s > M`. Thus the **normalized** full-dissipation transport excess is pointwise unbounded above on every terminal tail, unlike the previous raw result. The same canonical `τ,N,K,C,δ,v` first-crossing witnesses are reused; no new hypotheses are introduced.

This is a pointwise tail-spike consequence, not an integrability estimate or unconditional continuation. It remains possible for a function to be pointwise unbounded and integrable. The separate signed-growth theorem proves L¹ nonintegrability under the same premises.

Lean additions:
- `h3Path_scalar_cofinalEscape_forces_unboundedLogDerivativeEveryTail244`
- `h3Path_cofinalPhysicalEnergyEscape_forces_unboundedNormalizedSignedMargin244`
- `h3Path_cofinalPhysicalEnergyEscape_excludes_normalizedTransportTailCeiling244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_unboundedNormalizedSignedTransport244`

Offline structural/registrar tests only; run pinned Lean and Lake locally.
