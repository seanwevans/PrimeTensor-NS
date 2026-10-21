# Exact middle/top phase coupling for normalized Fourier variance

Checkpoint: `05cced24` — exact signed fifth/cubic phase defect.

## Orientation of the signed phase remainder

Let `A = E0 D3`, `R = 1 - E2²/A`, `E0'=L0` and `E2'=L2-T2` (the zeroth-order transport vanishes). The previously proved exact identity

    D3' + M5 + P = M3,   P >= 0

produces the signed normalized variance concentration source

    X/A² = [2 E2 (L2-T2) A - E2² L0 D3]/A²
           + E2² E0 (M5 + P - M3)/A².

The exact phase remainder `P` has **positive** coefficient in `X/A²` and hence a **negative** coefficient in the derivative `R'=-X/A²`. In particular P is not an automatically stabilizing factor. This is crucial: the earlier signed top-dissipation estimate goes in the wrong direction for an upper concentration bound.

The second term is exactly

    E2² E0 (M5-M3)/A² + E2² E0 P/A².

On the positive kinetic branch, the phase penalty is nonnegative.

## Fifth-free middle coupling bound

The already proved physical `|T2| <= 18 h E2`, `E2² <= E0 D3`, `L2 <= 0`, and `L0 <= 0` imply

    [2 E2 (L2-T2) A - E2² L0 D3]/A²
       <= -(L0 D3)/A + 36 h.

Unlike the earlier global viscous ceiling, the middle budget has no fifth moment. A near-Young secant must therefore be supported by the explicitly SIGNED `(M5 + P - M3)` top contribution, after the kinetic diffusion and order-two transport allowance. This is a necessary condition, not a terminal bound or continuation theorem.

## Research implication

The phase defect can *favor concentration of normalized moment ratios* while penalizing positive top-dissipation growth. To make progress toward a genuine exclusion of blowup, derive a cancellation involving `E2'` or improve estimates for the signed pair `M5+P-M3` rather than simply bounding `P` below. This checkpoint makes the sign obstacle explicit in the physical Lean hierarchy.
