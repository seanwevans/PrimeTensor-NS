# Exact-anchor physical H³ exposure intermittency and supercubic alternative

Base: `24c12b23` — prove canonical H3 full physical dissipation exposure collapse.

## Physical result

Write `R_k = v(k)+1`, `δ_k=δ(v(k))`, `D_k = D₃(τ(v(k)))` and
`I_k = ∫_{τ(v(k))}^{τ(v(k))+δ_k} D₃(t) dt`. The *same* exact-anchor
canonical source-maximizing, minimal-annulus, disjoint windows satisfy

    ∑ I_k < ∞,    I_k → 0,    D_k > (3/4) R_k³ → ∞,
    I_k ≥ (δ_k/2) R_k³,    δ_k > 0.

Dividing the genuine physical lower charge by the genuine window width,

    I_k / δ_k ≥ R_k³/2 → ∞.

This identifies a rigorous spatiotemporal intermittency regime: the ACTUAL
mean full physical H³ dissipation diverges while each ACTUAL dissipation
integral tends to zero. From `δ_k R_k³ ≤ 2 I_k` we also get

    δ_k R_k³ → 0.

For *every* fixed `M ≥ 0` and `ε > 0`, eventually either

    δ_k D_k ≤ ε   OR   D_k > M R_k³.

This is a sharp necessary alternative independent of any critical annular
width cap. If a hypothetical noncollapsed physical peak-height charge
`η ≤ δ_k D_k` holds EVENTUALLY for a fixed `η>0`, its first branch is
excluded for `ε=η/2`, forcing

    D_k / R_k³ → +∞.

The antecedent `η ≤ δ_k D_k` is **not** asserted by the physical PDE.
It describes precisely what extra full-dissipation persistence would cost.
No uniform continuity modulus for the unbounded H³ dissipation functional,
critical ninth/eighth width cap, smooth extension, or global regularity is
established.

## Lean statements

1. `h3Path_scalar_cubicCharge_forces_divergingWindowMean244`
2. `h3Path_scalar_cubicCharge_forces_scaledWidthCollapse244`
3. `h3Path_scalar_smallCubicClock_or_supercubicHeight244`
4. `h3Path_scalar_noncollapsedPeakCharge_forces_supercubicRatio244`
5. `h3Path_noL2Trace_exactAnchor_physicalExposureIntermittency244`

The last theorem transports all conclusions through the SAME witnesses
from the previously verified exact-anchor physical-exposure theorem. All
baseline hypotheses (no strong terminal L² trace and finite full H³ time
integral included) are explicit. This patch has not been compiled by local
Lean/Mathlib in the packaging environment.
