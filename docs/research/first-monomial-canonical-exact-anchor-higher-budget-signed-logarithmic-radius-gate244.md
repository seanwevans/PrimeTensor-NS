# All-orders physical signed logarithmic H³ radius gate

Base commit: `4135f70f` — quantify all-orders critical H3 radius by physical signed transport secants.

At the same disjoint canonical exact-anchor witnesses, the previously proved fourth-power exponential secant inequality holds under the explicit higher-moment majorant, attained projected source ceiling, eighth-power outer cap, epsilon smallness and weighted terminal clock noncompression.

Write `R_k = v(k)+1`, `t_k=τ(v(k))`, `E_b=velocityH3EnergyAt u b`, and the exact normalized physical full-dissipation transport excess `g(s)=max(0,(-T_H3(s)-2 D_3(s))/E_3(s))`. For each fixed b ∈ (a,T), eventually an interior physical time s∈(b,t_k) satisfies

    R_k^(16m+3) ≤ A (B exp((t_k-b)g(s))+1)^4,
    A=(512 ε²)^4 D^5,
    B=2304 E_b S² ≥0.

Since R_k≥1, the above inequality forces `A>0`. Since `(t_k-b)g(s)≥0`, `exp((t_k-b)g(s))≥1`, so `B exp(x)+1 ≤ (B+1) exp(x)`. Raising to the fourth power and taking real logarithms yields

    (16m+3) log R_k ≤ log(A (B+1)^4) + 4 (t_k-b) g(s)

and, since 0<t_k-b<T-b and g≥0, also

    (16m+3) log R_k ≤ log(A (B+1)^4) + 4 (T-b) g(s).

This is a *quantitative necessary lower rate* for normalized signed transport at an intermediate physical time. The logarithmic coefficient is fixed in k. It is not a pointwise bound at the prescribed canonical time t_k, nor does it establish the radial moment, source, geometric or terminal-clock hypotheses from the PDE.

Lean declarations:
- `h3Path_higherBudget_signedExpFourth_forces_logRadiusBudget244`
- `h3Path_higherBudget_logRadiusBudget_to_terminalGap244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_signedLogRadiusGate244`

Offline structural checks only. Full Lean compilation requires the pinned repository Lake toolchain.
