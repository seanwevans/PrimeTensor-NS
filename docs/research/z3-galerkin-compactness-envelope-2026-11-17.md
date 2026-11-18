# Constructed finite Z³ Galerkin: spectral tail and equicontinuity envelope

## Starting result

Repository HEAD `a6f9f168d` verifies the exact finite-dimensional viscous-plus-full-Leray
Galerkin flow on the same **closed** interval `[a,a+τ]` for every finite cutoff `S`,
where `τ = (log 2-log(9/5))/100 = log(10/9)/100`. Its genuine Fourier coefficients satisfy
`W_(log 2-100(t-a))(u_S(t)) ≤ 100`. This module makes the key compactness
consequences explicit and independent of the number of retained lattice modes.

## Quantitative spectral tail

For any pair of analytic radii `r ≤ R`, real threshold `N`, and a finite set
`S` of frequencies with degree `d(n)=∑_{j=1}^3 |n_j|`, the weighted tail obeys

    Σ_{n∈S,d(n)≥N} exp(r d(n)) |u_n|
       ≤ exp(-(R-r) N) · W_R(u_S).

The proof is termwise radius reserve plus **one** positivity-based subset-sum
comparison. In particular `R=log(9/5)`, `r=log(3/2)` and
`W_R(u_S(t)) ≤ 100` yield

    Σ_{n∈S,d(n)≥N} (3/2)^{d(n)} |u_{S,n}(t)| ≤ 100 (5/6)^N

for every integer `N≥0`, uniformly in both `S` and `t∈[a,a+τ]`. The Lean theorem
uses the equivalent real-exponential expression valid for all real thresholds.

## Closed-time equicontinuity

The verified `51000` estimate on the **actual** finite Leray coefficient vector field
makes every constructed solution `51000`-Lipschitz on the **closed** interval:

    ‖u_S(t)-u_S(z)‖_Pi ≤ 51000 |t-z|.

The coefficient/state dimension varies with `S`, but neither constant does.
The final dependent-choice existence theorem builds an entire cutoff-indexed family
of trajectories satisfying both bounds, without assuming solutions as input.

## Mathematical boundary

This is the uniform spectral tightness and time-equicontinuity input for a
Fourier-space Arzelà–Ascoli/diagonal limit. It does **not** prove a convergent
subsequence, convergence of the full nonlinear Leray convolution, conservation
of any physical constraint under cutoff limits, or Navier–Stokes regularity
outside the verified analytic window. Proving a suitable cutoff limit is next.

The Lean file is subject to actual elaboration and build on the pinned
`leanprover/lean4:v4.34.0-rc1`/mathlib toolchain; static checks do not substitute for Lean.
