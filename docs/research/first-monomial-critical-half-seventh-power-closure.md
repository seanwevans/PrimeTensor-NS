# Exact seventh-power route to classical critical-half control

Base checkpoint: `0acf2b2c` (critical-half interpolation and terminal-scope audit).

This module is an **algebraic closure** of the classical critical-half bound,
not a new nonlinear inequality and not a proof of the remaining Sobolev step.
The actual first monomial is the real signed sum over 243 slots of a product of
orders 3, 2 and 2. Standard Hölder with `L² × L⁴ × L⁴` and the classical
homogeneous Sobolev embedding `Ḣ^(3/4)(ℝ³) -> L⁴(ℝ³)` give its finite constant.

For a single aggregate, let `H` represent the Ḣ³ norm, `Q` the product of the
L⁴ norms of the two second-derivative factors (including the finite coordinate
sum constant), `A` the Ḣ^(1/2) norm, and `B` the Ḣ⁴ norm. The interpolation
exponents are

    H <= A^(2/7) B^(5/7),
    Q <= K A^(5/7) B^(9/7).

The second line uses two L⁴ factors, each at derivative order `11/4`, hence
one exponent `5/14` and `9/14` for each factor. Raising both displayed
inequalities to the seventh power eliminates all fractional real powers:

    H^7 <= A^2 B^5,     Q^7 <= K^7 A^5 B^9.

Multiplication yields `(H Q)^7 <= (K A B²)^7`, so nonnegative real powers
imply `H Q <= K A B²`, including all zero-norm cases. The Lean scalar proof is
fully division-free and preserves the coefficient K introduced by the actual
Sobolev inequalities.

If `A² <= E0+E1` and `B²=D`, the same algebra gives

    |M| <= K sqrt(E0+E1) D.

These last estimates are also packaged for the repository's physical Schwartz
symbols without changing their definitions.

## Still unproved in this module

1. The physical Schwartz 2-4-4 Hölder bound with exact five-index summation.
2. The quantitative homogeneous Sobolev `Ḣ^(3/4) -> L⁴` estimate under the
   project's physical/Fourier normalization.
3. The fractional Hilbert norm interpolation and physical norm identification
   needed to *construct* H, Q, A and B.

The endpoint estimate is known classical analysis; formalizing it will **not**
close large-data three-dimensional Navier–Stokes regularity. The purpose of
this file is to pin down, and kernel-check, the exact exponent arithmetic that
an eventual unconditional Sobolev proof must instantiate, not to replace the
analytic argument with an assumption.
