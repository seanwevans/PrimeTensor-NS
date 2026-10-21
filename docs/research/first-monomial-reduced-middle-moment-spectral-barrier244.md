# Physical H³ reduced-middle-moment spectral barrier

Base: `9dd33359` — retain physical first-Cauchy Fourier variance in sharp H³ Young absorption.

## Analytic result

Let `E` denote physical H³ energy, `E₂` its second-order block,
`E₃` its third-order block, and `D₃` its third-order Fourier dissipation.
The second Cauchy inequality `E₃² ≤ E₂ D₃` implies `D₃=0 -> E₃=0`.
Thus the following fully defined normalized middle-moment cost uses
Lean's total division without a positive-dissipation hypothesis:

    R(t) = (27/256) K(t)^4 [E₂(t)^2/D₃(t)] / E(t),
    K(t) = 4398 C₁ sqrt(E(t)).

The sharp variance-corrected Young estimate gives

    (K(t) E₃(t) - D₃(t))/E(t) <= R(t)

at every strict energy-class time, including `D₃=0`.  After kinetic
anchoring, the physical logarithmic energy slope satisfies

    E'(t)/E(t) <= K_b + R(t),
    K_b=(3C₁+441C₁²) E₀(b).

The existing *essential* top Landau margin barrier transfers to R:
under hypothetical nonextension, on every strict post-anchor subtail
R defeats every integrable a.e. majorant, hence every fixed a.e. ceiling.
Conversely `IntegrableOn R (Ioo d T)` suffices for smooth continuation.

By the first-Cauchy defect `F₁=E₀D₃-E₂² ≥ 0`, when `D₃>0`

    E₂²/D₃ = E₀ - F₁/D₃ <= E₀.

Thus R is the variance-corrected remainder, not the original full-kinetic
Young cost. Its integrability is **not** proved.  In particular no uniform
spectral variance floor or finite-time regularity theorem is asserted.

## Checks

Register with `tools/audit/register_first_monomial_reduced_middle_moment244.py`;
regenerate `proof/order.txt`; run fragment checks, the Lean target, the
entire Lake build, and `tools/audit/baseline.sh --reuse-build` before push.
