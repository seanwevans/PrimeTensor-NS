# Physical H³ exact-anchor half-gap budget and high-Q tail dichotomy

Base commit `f6c8cf5f`: force canonical H3 high-tail mass or projected-source impulse escape.

## Central new bound

The exact quadratic-sharp canonical width is the minimum of four caps. Its linear cap guarantees Λ δ ≤ gap/4, and its independent square-root cap guarantees Ξ δ² ≤ gap/4. Thus Λ δ+Ξ δ² ≤ gap/2. This is strictly stronger than the previously exported `Λδ+Ξδ² < gap` interface.

The whole one-cutoff LOW-Q rate consists of the Q-term inside the annular R/Q coefficients, and all missing R-terms are nonnegative. Therefore the one-cutoff source-driven PDE budget is ≤ gap/2. Since the exact gap = (L_Q-L_R)(anchor) - R³/2 < full physical D₃(anchor), we obtain the unconditional-on-source bound

    Λ_Q δ + Ξ_Q δ² < D₃(anchor) / 2.

This requires the ORIGINAL exact canonical selector, real PDE rates and physical annulus partition. It is not a generic statement about arbitrary shorter windows or source growth.

## Genuine physical dichotomy

The previously proved physical temporal-cliff theorem says each sufficiently late canonical window either has `δ D(anchor) ≤ η`, or contains a real time `s` with `D(s)< D(anchor)/4`. The verified one-cutoff modulus and high-Q partition then give

    H_Q(anchor) > D(anchor)/4,

because the low-Q change costs less than D(anchor)/2, and the high-Q tail at `s` is nonnegative. Thus for every η>0, eventually

    δ D(anchor) ≤ η OR H_Q(anchor) > D(anchor)/4.

This new result has **no extra small-relative-PDE-budget or critical annular-width hypothesis**. It preserves the exact original τ,N,K,C,δ,v witnesses, source maximum and strictly disjoint windows. The high-tail conclusion conditional on a fixed positive eventual anchor-height charge also follows, but the positive-charge premise is still **not automatic**.

## Formal declarations
- `h3Path_quadraticSharpWidth_halfGapBudget244`
- `h3Path_outerLowPDEBudget_le_annularBudget244`
- `h3Path_exactAnchor_outerLowBudget_lt_halfDissipation244`
- `h3Path_exactAnchor_quarterCliff_forces_quarterHighTail244`
- `h3Path_noL2Trace_exactAnchor_chargeOrQuarterHighTail244`

Compilation of the Lean file itself is not available in the packaging container; the local pinned Lake build is required.
