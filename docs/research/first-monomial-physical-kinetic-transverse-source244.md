# Exact physical kinetic/transverse momentum-source split

Base commit: `f074cbe3` — derive vanishing terminal kinetic dissipation and signed source action.

The canonical physical Hilbert velocity `U` and projected source `R` satisfy
`‖U‖² = E₀` and `⟪U,R⟫ = -D₀`. The new division-free source

    W = E₀ R + D₀ U

is orthogonal to `U` without a lower bound on `E₀`. On strictly positive kinetic mass, define

    Q = R + (D₀/E₀) U.

Then `E₀ Q = W`, `⟪U,Q⟫ = 0`, and the exact Hilbert Pythagorean identity is

    ‖R‖² = ‖Q‖² + D₀²/E₀.

It refines the Cauchy–Schwarz source-cost estimate. `Q` is the part of the
physical momentum source that is **invisible** to scalar kinetic dissipation.
The established terminal kinetic infimum gives `E₀(t)>0` on an H³ class tail
when that infimum is strictly positive, so the decomposition is valid all
along the tail without time-by-time positivity assumptions.

This does not establish integrability of `Q`, boundedness of high-order H³
dissipation, strong physical L² convergence at `T`, or smooth continuation.
It uses the previously proved strong physical projected momentum derivative
and the old-path energy conservation/cancellation chain. It does not offer
an independent replacement for their curl weak-FTC dependency.

## Suggested next theorem

Under strictly positive terminal kinetic mass, prove that the radial component
`(D₀/E₀) U` has a finite terminal L¹-in-time norm, using the already-closed
exact kinetic terminal-tail budget. The remaining possible L¹ obstruction
would be the transverse source `Q`. This analytic integrability step is **not**
proved in the present module.
