# Prescribed Fourier initial data: constructive local infinite Navier–Stokes evolution

Date: 2026-11-18. Parent: `1b8d7f3fe6b549284c63ffa1fc2bee2333932088`.

## The mathematical distinction

The existing theorem `thirdFullThreeBand_z3Galerkin_orderedLerayIntegralEquation244` proves the time integral identity *provided* Galerkin trajectories, uniform Fourier/source limits, and an identified source are all available for a common subsequence. This module assembles those facts with **one prescribed infinite initial Fourier field**. It does not assume an infinite PDE solution, a preselected convergent Galerkin family, or a limit convolution identity.

Let `u0 : ℤ³ → ℂ³` satisfy `Summable ((2^|n|₁) ‖u0 n‖)` and its actual infinite `W_log 2` sum strictly less than 100. Let `s k` be **arbitrary finite** cutoffs which eventually contain each fixed `n ∈ ℤ³`. The finite initial data `x0 k` are the exact restriction of `u0` to `s k`, rather than an unrelated family. The summability/strict bound gives the finite `W_log 2` condition for the actual finite-dimensional ODE existence theorem, without any cutoff-cardinality loss.

From genuine ODE paths, take the single `Arzelà–Ascoli + Tychonoff` mode subsequence, obtaining complete `W_log(3/2)` state convergence and the `W_log(9/5) ≤ 100` mass at every limit time. Apply the existing all-output `W_log(5/4)` Cauchy theorem to **the same subsequence**, construct its completed nonlinear source with `W_log(5/4) ≤ 50,000`, and identify it with the absolutely convergent infinite ordered Leray convolution. A uniform source-mode lemma and the committed temporal FTC allow passage of each *retained* coefficient ODE. Since exhaustion survives any strictly monotone subsequence, every fixed coefficient is eventually retained. On the initial slice, those retained coefficients agree exactly with `u0 n`, giving the prescribed initial trace by uniqueness of coordinate limits.

## Conclusion

For `0 ≤ μ ≤ 1/10`, on the cutoff-independent interval `Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a)`, the theorem gives a Fourier field `g` with time-continuous individual coefficients, a summable high-analytic-radius Wiener norm at most 100, and source norm at most 50,000, satisfying for every Fourier mode `n` and every time `t` in the closed interval:

`g(t,n) - u0(n) = ∫_a^t [ - μ ‖ξ_n‖² g(r,n) + Σ_p (-i P_n)[((n-p)·g(r,p)) g(r,n-p)] ] dr`.

The inner ordered convolution is absolutely convergent. It is the *exact* complex Leray projected quadratic Fourier source (not a scalar surrogate), and the Fourier equation holds coefficientwise. No nestedness or Fourier-cube geometry is assumed beyond cutoff exhaustion. A separate theorem proves that the canonical cubes `thirdFullThreeBandZ3GalerkinFixedCoreCube244 k` satisfy that condition, giving a concrete instantiation.

## Scope boundaries and follow-up

This is local existence for the projected complex `ℤ³` Fourier equation. It is not a solution to the physical `ℝ³` Clay problem, not global H³ continuation, and not yet an assertion that arbitrary data define real, divergence-free Navier–Stokes velocity: divergence-free, Hermitian reality, zero-mode handling, and spatial reconstruction need their own invariant-subspace bridge. Next work: specify solenoidal/Hermitian initial data and prove those invariants pass from finite ODEs, then a real periodic physical-space reconstruction (and separate `ℝ³` theory).

There are no new axioms and no proof placeholders. Compilation must be performed with the repository's pinned Lean/mathlib toolchain; static source audit does not prove compilation.
