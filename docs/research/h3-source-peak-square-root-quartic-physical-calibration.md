# Sharp square-root frequency calibration of physical H³ source peaks

Base `df296d97`. The previous constructive radius `R_old = Q+1+A²B/P²`, where
`Q=max(1,σ)`, `P>0` is the actual projected highpass source excess,
`A=3+C_L(‖U(t)‖+E)` and `B=12C²+2(D_full(t)+M)≥0`, exceeds what the physical
PDE source-drop inequality requires. Its actual prerequisite is only
`R²P²>A²B`, so choose

    R_sqrt = Q+1+sqrt(A²B)/P,
    δ_sqrt = min(w,R_sqrt⁻⁴).

Then `R_sqrt≥max(1,σ)`, `R_sqrt²P²>A²B`, `δ_sqrt>0` and on the true physical
PDE `D_>σ(s)>M` throughout the short interval. For nonnegative `B`,
`R_sqrt ≤ R_old` need not hold when `sqrt(A²B)` is small (<1 in appropriate
units); there is nevertheless no artificially squared large-cost scaling.
For large `A²B/P²`, the previous clock compressed as the fourth power of
that ratio, rather than the square of it.

The existing no-terminal-L²-trace source-driven cofinal windows now admit
these recalibrated widths on the *original* pairwise-separated positive
intervals, using compact-time physical source and spectral continuity.
Full physical H³ dissipative costs are retained as extended integrals.

## Improved denominator-free charge

Because `R_sqrt P = (Q+1)P + sqrt(A²B)`, and
`(x+y)⁴≤4(x²+y²)²`, the exact normalized scale satisfies

    R_sqrt⁴ P⁴ ≤ 4[((Q+1)² P² + A²B)²].

If `M>0,J>0` and the calibrated window's physical dissipation charge
satisfies `M δ_sqrt ≤ J`, then necessarily

    w ≤ J/M  OR  M P⁴ ≤ 4 J [((Q+1)² P² + A²B)²].

The source-margin polynomial degree is now four rather than eight.
No global H³ continuation, uniform upper PDE ceiling, or nonsummability
conclusion is asserted. A global contradiction still needs new energy or
source-geometry information controlling these local quantities.

The package is statically audited; proof compilation requires the pinned
repository Lean/mathlib toolchain.
