# Exact-anchor cubic dissipation escape and physical normalized rate

Base: `62a649af` — force canonical H3 anchor spectral and dissipation escape under critical width.

## New mathematical step

The original exact-anchor canonical disjoint sequence has a strict first-crossing annular gap

    (v_k+1)^3 / 4 < [L_Q(U(τ_k)) - L_R(U(τ_k))] - (v_k+1)^3 / 2.

The existing physical annular-to-full-dissipation theorem proves

    L_Q(U(τ_k)) - L_R(U(τ_k)) <= D_3(τ_k).

Combining these yields a genuine **pointwise physical dissipation floor**

    3(v_k+1)^3 / 4 < D_3(τ_k)

at every original cofinal anchor, independently of any critical-width, geometric noncompression, or linear-rate bound. As `v` is strictly monotone, `D_3(τ_k) → +∞`. This is a stronger conclusion than the previous critical-width-conditional dissipation escape and is not an unconditional regularity claim: the no-terminal-strong-L²-trace and finite full-H3 dissipation premises remain explicit.

Independently, the original pairwise disjoint windows carry a nonnegative summable cost

    Sum_k δ(v_k) (v_k+1)^3 / 2 < infinity.

Thus `δ(v_k) (v_k+1)^3 → 0`. This demonstrates how arbitrarily large pointwise dissipation and finite total dissipation coexist: the exact persistence widths collapse faster than the cubic scale.

If a fixed critical ninth/eighth-width cap also holds eventually, the previous exact-anchor theorem gives `E_3(τ_k) → +∞`, `K_k=‖U_3(τ_k)‖ → +∞`, and `D_3(τ_k)/K_k² → +∞`. The actual three-component energy identity implies `1 ≤ E_3(τ_k) ≤ 1+3K_k²`. Hence eventually `E_3(τ_k) ≤ 4K_k²`, upgrading to the **physical energy-normalized** ratio

    D_3(τ_k)/E_3(τ_k) → +∞.

Equivalently, for each fixed real `M`, eventually `M E_3(τ_k) ≤ D_3(τ_k)`. This is a pointwise, not time-integrated, absorption statement; it supplies no lower bound on how long a high normalized dissipation rate persists.

## Lean declarations

1. `h3Path_scalar_cubicFloor_forces_dissipationEscape244`
2. `h3Path_scalar_spectralRateEscape_forces_physicalEnergyRate244`
3. `h3Path_scalar_summableCubicWindowCost_forces_clockCollapse244`
4. `h3Path_noL2Trace_exactAnchor_unconditionalDissipationEscape_conditionalRate244`

This package does not assume an unproved source bound or conclude Navier–Stokes regularity. The strict physical H3 preterminal hypotheses and no-L²-trace branch remain as in the existing proof chain.

Local `lake` compilation and the pinned Mathlib audit must be performed in the user's repository; not available in the packaging runtime.
