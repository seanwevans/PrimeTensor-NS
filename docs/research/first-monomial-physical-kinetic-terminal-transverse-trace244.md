# Physical kinetic terminal L² trace from transverse source action

Baseline `c5b9da89` — *bound longitudinal source expenditure and transverse velocity variation*.

## Analytic interfaces and actual theorem gain

Let `U(t)` be the genuine old physical L² Hilbert velocity, `R(t)` the actual
projected source, `D₀(t)` the order-zero viscous dissipation, and
`E₀(t) = ‖U(t)‖²`. On a strict H³ energy-class tail `(a,T)`, the canonical
kinetic terminal infimum `L` is already finite, nonnegative, and is the
limit of `E₀(t)` as `t ↑ T`.

The previous theorem gives, for `L>0` and `a<s≤t<T`, the *exact-source-based*
quantitative displacement estimate

    ‖U(t) - U(s)‖ ≤ ∫_s^t ‖Q(r)‖ dr + (E₀(s)-L)/(2√L),

where `Q(t) = R(t) + (D₀(t)/E₀(t)) U(t)` is perpendicular to the velocity.

The definition `H3PhysicalTransverseTerminalTailVanishing244 hH3` is the
explicit remaining hypothesis: for every positive epsilon, sufficiently late
`s` have `∫_s^t ‖Q‖ < epsilon` simultaneously for all later strict `t`.
This hypothesis is **not** derived from `D₀` or the signed cubic/triad budget.

### Main consequences

1. When `L>0`, transverse vanishing implies uniform Cauchy estimates for
   `U(t)` on all later strict times.
2. Hilbert completeness upgrades the Cauchy estimate to a genuine strong
   physical L² terminal trace `U_T`.
3. When `L=0`, the kinetic energy identity alone yields `U(t) → 0` strongly;
   no transverse hypothesis is required.
4. Under the transverse condition, both cases combine into a strong trace
   whose squared physical L² norm is exactly `L`.
5. Every strong physical terminal trace, however obtained, satisfies
   `‖U_T‖² = L` by uniqueness of the scalar kinetic limit.

This module closes a **conditional physical L² trace criterion**, not a
strong H³ trace, terminal vorticity trace, or Navier–Stokes continuation.
The positive-limit transverse variation condition is a genuine remaining
analytic problem. All theorems inherit the earlier physical evolution branch.
