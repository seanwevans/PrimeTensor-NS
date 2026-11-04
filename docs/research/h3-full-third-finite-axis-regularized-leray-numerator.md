# Fin-index Leray symbol and intrinsic-axis regularized numerator

Baseline: `a05ec4ee`, 2026-11-04.

The repository has two separately formalized Fourier realizations:

- the finite-index `h3LerayCoefficient ξ i j` from the genuine H³ solver, whose derivative symbol is `2π i ξ_j`;
- the complex-bilinear transverse numerator `thirdFullComplexTransverseNumerator244 ξ A` on `Axis Depth.three → ℝ` used to construct actual real solenoidal Schwartz fields.

This patch proves their **exact pointwise equality after multiplication by the squared Fourier radius**, including at frequency zero. The proof first multiplies the Leray matrix by `h3FourierGradientSquare`, avoiding singular division and using `h3FourierDerivativeSymbol_eq_zero_of_gradientSquare_eq_zero` at zero. The finite sum is converted through the actual Fin-three/axis equivalence. The nonzero constant `2πi` cancels by `Complex.two_pi_I_ne_zero`, without dividing by `‖ξ‖`.

The final theorem is

```
Rₙ(ξ) ∑ⱼ Pᵢⱼ(ξ) zⱼ
  = 1/(‖ξ‖² + δₙ) N_ξ(z)_i.
```

Here `δₙ = 1/(n+1)` and `Rₙ = ‖ξ‖²/(‖ξ‖² + δₙ)`. This identifies the smooth numerator constructed in the immediately preceding commit with the original finite Leray projector, at the level of exact pointwise functions.

**Remaining analytic step:** use `h3SpectralFinLerayApply_ae` and the existing compact-Hermitian spectral approximants to identify the full `L²` equivalence classes. The physical input must be the *deweighted* compact representative (not the weighted solver state itself), using `h3SmoothCompactDeweightedSchwartz` and `h3SobolevFrequencyWeight` to avoid a false Fourier normalization. Then the previously proved diagonal limit gives unconditional real solenoidal Schwartz density. Neither full density nor physical E₂/E₃ jet matching is claimed in this module.

Lean compilation is not available in the packaging environment. The module is intended to be checked by the repository's pinned Lean toolchain before commit.
