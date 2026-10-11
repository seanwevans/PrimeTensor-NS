# Initial relative-energy uniqueness with a variable time coefficient

Base commit: `dd0c60cd` — derive initial uniqueness from positive-time relative energy residuals.

## Reduction proved

The prior positive-time estimate uses a tolerance-dependent constant `κ`. Here
one may instead supply a time-varying coefficient `κ_ε(t)` and an error
density `R_ε(t)` satisfying, at every `0 < t ≤ b`,

```text
e(t) ≤ κ_ε(t) * ∫₀ᵗ e(s) ds + ∫₀ᵗ |R_ε(s)| ds
κ_ε(t) ≤ K
∫₀ᵇ |R_ε(s)| ds ≤ ε.
```

Because `e ≥ 0`, its forward interval integral is nonnegative, and therefore
`κ_ε(t) ∫₀ᵗ e ≤ K ∫₀ᵗ e`. This proves the *previous* fixed-coefficient
epsilon-residual interface; no regularity of `κ_ε` is necessary.

The module additionally proves a scalar zero-energy theorem using the
already formalized integrable scalar Gronwall argument and exposes the
physical initial trace, compact weak-test comparison and conditional full-time
transverse consequences.

## Analytic obligations not discharged

- Actual old/selected relative-energy comparison against the canonical
  Banach-selected mild solution.
- Time-integrability and strict-positive continuity of the comparison energy.
- Uniform upper bound on the time-variable coefficients and residual errors
  whose total absolute time mass can be made arbitrarily small.
- Separate strong-H³ terminal vorticity endpoint for the full-time theorem.

This patch does not prove the Navier--Stokes millennium regularity problem.
