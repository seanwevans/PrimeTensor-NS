# High-Q spectral dissipation evacuation at exact canonical temporal cliffs

Base commit: `bc94d2bb` — force canonical H3 physical temporal cliffs into exterior spectral evacuation.

## New physical statement

The prior analysis charged full H³ temporal cliffs to *the combined exterior* `L_R+H_Q`, subtracting the anchored finite-annulus variation budget. The actual source-driven PDE estimate controls the entire low-frequency dissipation `L_Q` directly. The physical radial partition therefore gives, on exactly the same canonical window:

    (1-θ) D₃(t) - [Λ_Q δ + Ξ_Q δ²] < H_Q(t) - H_Q(s)

when `D₃(s) < θ D₃(t)`, with

    Λ_Q = 6(Q+1) K V_Q(C),    Ξ_Q = 3 V_Q(C)^2,
    V_Q(C) = (Q+1) sqrt(3 W_Q) C.

Here `Q=N(vk)+1`, `K=‖U₃(τ(vk))‖`, and `C` is the attained physical Leray-projected source envelope on the original half-terminal interval. This is a **genuine high-frequency** dissipation decrease, rather than a signed or arbitrary remainder. The original exact quadratic-sharp clock and disjoint anchors are preserved.

With an *additional* relative budget hypothesis

    Λ_Q δ + Ξ_Q δ² ≤ α D₃(t),

the exact positive physical high-frequency mass at the anchor satisfies

    (1-θ-α) D₃(t) < H_Q(t).

The bound is quantitatively positive if `θ+α<1`. Neither this relative-budget bound nor the eventually nonvanishing peak-charge premise `δ D₃(τ(vk)) ≥ η>0` is derived automatically. In particular, no high-frequency escape conclusion from finite H³ dissipation alone is asserted.

## Lean declarations

- `h3PathCubicAnnulusOuterLowLinearRate244` (definition)
- `h3PathCubicAnnulusOuterLowQuadraticRate244` (definition)
- `h3Path_physicalHighTail_outerPartition244`
- `h3Path_physicalPDE_cliff_forces_highTailEvacuation244`
- `h3Path_exactAnchorPDE_dip_forces_highTailEvacuation244`
- `h3Path_scalar_lowBudget_highTail_anchorLower244`
- `h3Path_noL2Trace_exactAnchor_persistentCharge_highTailEvacuation244`

The Lean/Mathlib compilation is not available in the packaging container; run the pinned Lake build and audits locally.
