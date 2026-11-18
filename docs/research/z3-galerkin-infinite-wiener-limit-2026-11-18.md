# The actual infinite Fourier Wiener limit of the constructed Galerkin flows

## Scope and hypotheses

Input is the proven finite-dimensional strong Navier–Stokes Galerkin ODE family on the shared closed time interval, with strict initial `W_(log 2) < 100`, and viscosity `0 ≤ mu ≤ 1/10`. Supports may be unrelated and initial states need not be mutually compatible. The preceding Arzelà–Ascoli module already gives a common Fourier-coordinate subsequence; the strong Wiener Cauchy theorem supplies an independent norm-Cauchy route.

## Mathematical advance

For every time `t`, the limit of the extracted zero-extended coefficient curves `g_n(t)` is an actual **infinite** `Z³` Fourier field with finite high-radius mass:

    ∑' n, exp(log(9/5)*degree(n)) * ‖g_n(t)‖ ≤ 100.

The proof passes a *finite* analytic mass inequality to the limit using coordinate convergence and finite-sum continuity, then invokes the real summability criterion `summable_of_sum_le`. There is no assumption that the limit series converges.

For every `ε > 0`, for all sufficiently late `k` and **all** times on the closed common interval,

    ∑' n, exp(log(3/2)*degree(n)) * ‖u_(S_(φ k))(t,n) - g_n(t)‖ < ε.

The crucial inequality holds for every finite partial sum first. Split that sum into frequencies of degree `< N` and the remaining tail. A fixed cube contains the low modes, while the reserve `log(9/5) - log(3/2)` gives the same dimension-free `200*(5/6)^N` tail for the finite Galerkin state **and** its infinite limit. Choose `N` before the index `k` so that this tail is small. Finite-coordinate uniform time convergence then controls the cube. The real infinite-sum comparison transfers that estimate to the complete `ℓ¹` series.

## Exact outcome

The module defines `thirdFullThreeBandZ3InfiniteWienerMass244` and constructs honest Galerkin strong ODE paths, a common increasing subsequence, continuous limit curves at every mode, high-radius summability of the infinite Fourier limit, and uniform-time convergence in the full lower-radius infinite mass.

**Not proved here:** that the limit satisfies the full infinite Navier–Stokes Leray equation; convergence of the differentiated quadratic source; divergence-free and Hermitian inheritance for arbitrary unconstrained initial Galerkin data; an infinite-dimensional classical/weak PDE solution; or Clay's global continuation result. The next proof must also specify compatible fixed infinite initial data and exhaust the integer lattice to identify the intended Cauchy problem.

## Reproducibility

`lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdSolenoidalKineticThreeBandZ3GalerkinInfiniteWienerLimit.lean` is the first decisive compile check. No tactic uses `sorry`, axioms, or unsafe evaluation. The Python static checker validates declarations and scope but does **not** replace Lean compilation.
