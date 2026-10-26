# Exact cofinal cubic H³ PDE clock and concentration alternative

Base commit: `489d8c07` (*derive cubic H3 persistence clock collapse under finite terminal dissipation*).

## Mathematical progress

The previous cofinal cubic annulus result recorded an existential persistence width `δ` with a strict anchored-PDE polynomial budget. The new module preserves the *exact choice* of width

\[
\delta=\min\left\{\frac{b}{2},\ 1,\ \frac{g}{2(\Lambda+\Xi+1)}\right\},\qquad b=\frac{T-t}{2},
\]

where `g` is the annular cubic-height surplus, `Λ` is the linear physical projected-source variation coefficient, and `Ξ` is the nonnegative quadratic coefficient. This exact minimum satisfies `δ > 0`, `δ < b`, and `Λδ+Ξδ² < g`.

The module supplies:

1. A direct proof for the exact minimum, not just an existential selector.
2. A three-way algebraic cost alternative under `A δ ≤ M`: either `2M ≥ A b`, or `M ≥ A`, or `Ag ≤ 2M(Λ+Ξ+1)`.
3. An actual one-witness finite-annulus theorem constructing `N,K,C,δ` from the physical path and its strictly interior projected momentum source continuity, retaining `δ`'s exact expression and the integrated half-cubic cost.
4. A cofinal no-terminal-physical-`L²`-trace witness sequence retaining exact widths at *every* index, prior to the disjoint subsequence selection.

## Next connection

One may apply `h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244` to these exact clocks; it **only selects indices** and does not shorten selected windows. If full terminal H³ dissipation is separately interval-integrable, the disjoint cost-sum theorem bounds `Aₖ δₖ` and the trichotomy then isolates terminal-time compression versus the PDE coefficient growth. The theorem here does not claim an unconditional terminal continuation or exclude either branch.
