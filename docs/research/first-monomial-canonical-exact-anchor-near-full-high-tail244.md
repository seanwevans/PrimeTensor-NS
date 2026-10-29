# Canonical H³ near-total high-tail alternative: exact low-Q persistence

Base: `c1d54829` — prove canonical H3 half-height persistence and near-half high-tail alternative.

## Exact new estimate

The sharp PDE width has separate linear and quadratic caps allocating no more than a quarter of its exact gap to each contribution. Therefore the whole outer low-Q rate budget is bounded by half the gap. The gap is the actual finite-annulus dissipation minus R³/2, and hence lies **strictly below** the actual low-Q anchor dissipation L_Q(t). The low-R term is nonnegative. Consequently:

    outer_low_Q_PDE_budget < L_Q(t)/2.

The already established physical projected momentum PDE modulus bounds the change in L_Q throughout each unchanged canonical window, so

    L_Q(s) >= L_Q(t)/2,
    D₃(s) >= L_Q(t)/2 for every s in [t, t+δ].

Because the full physical D₃ is integrable on [a,T],

    δ_k L_{Q_k}(t_k) <= 2 I_k,
    I_k = ∫_[t_k,t_k+δ_k] D₃(s) ds.

The same disjoint-window theorem shows ∑ I_k <∞ and I_k→0. Thus **the entire weighted low-Q anchor charge is summable** (and goes to zero). Via the exact radial partition L_Q(t_k) = D₃(t_k)-H_Q(t_k), this yields for every β<1 and ε>0, eventually

    δ_k D₃(t_k) <= ε  OR  β D₃(t_k) < H_{Q_k}(t_k).

If a fixed positive lower bound η≤δ_k D₃(t_k) persists eventually, then **for every fixed β<1**, the latter inequality holds eventually. This is an asymptotic 100% high-frequency fraction in the standard order sense. The crucial η hypothesis is NOT established by the PDE or finite dissipation. The moving Q_k is canonical, and no compact fixed-Q tail estimate is smuggled into this conclusion.

All conclusions are downstream of the original LoggedPreterminalH3PathAdmissible, PreterminalH3EnergyClass, positive terminal kinetic mass, no terminal physical L² trace, finite H³ dissipation integral and exact source-aware canonical clocks. No additional source ceiling, width cap or full-H³ temporal continuity hypothesis is added.

## Formal declarations

- `h3Path_exactAnchor_gap_lt_outerLowDissipation244`
- `h3Path_exactAnchor_outerLowBudget_lt_halfLow244`
- `h3Path_exactAnchor_fullDissipation_ge_halfOuterLow244`
- `h3Path_exactAnchor_outerLowIntegratedCharge244`
- `h3Path_scalar_lowWindowCharge_nearFullHighTail244`
- `h3Path_noL2Trace_exactAnchor_lowChargeOrNearFullHighTail244`


Packaging audits verify ZIP structure, declaration presence and registrar idempotence, but this module has not been compiled in the pinned Lean/Mathlib environment. Treat any local Lean error as requiring a follow-up correction; no formal certification is claimed before local compilation.
