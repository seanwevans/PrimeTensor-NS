# Z³ Galerkin fixed-core compactness bridge (17 November 2026)

**Base:** `d781e8b48ccb3c05ea1ff6c113dc0d7aad4fde32`.

## A genuinely finite, cutoff-independent Fourier core

The exact finite-dimensional Leray–Galerkin ODE now has a common closed analytic time interval and, for each finite cutoff `s`, an actual strong trajectory `γ_s`. The preceding compactness-envelope theorem gives `W_(9/5)(γ_s(t)) ≤ 100` uniformly in `s` and time.

For each integer `N ≥ 0`, define the *same finite set* of lattice modes for every cutoff:

`C_N = {n ∈ ℤ³ : -N ≤ n_j ≤ N for j=1,2,3}`.

Every mode with `|n|₁ < N` lies in `C_N`.

If `u_s` and `u_t` are zero-extended finite coefficient states belonging to arbitrary cutoffs `s` and `t`, the two analytic balls imply

`W_log(3/2)(s ∪ t, u_s-u_t) ≤ W_log(3/2)(C_N,u_s-u_t) + 200 exp(-N log(6/5))`.

The factor `200` is precisely the sum of two `100`-mass high-radius bounds. It does not depend on either cutoff, the number of output collisions, or the number of retained frequencies. The constant is unchanged if the cutoffs are not nested.

The proof uses three elementary but essential steps: (1) zero extension preserves Wiener mass under enlargement of finite support, (2) `W_r(u-v) ≤ W_r(u)+W_r(v)` and the already-verified two-radius exponential tail estimate, and (3) the low-degree part of either cutoff's output union lies in the fixed cube `C_N`.

## Constructed-flow consequence

The final theorem chooses **two actual strong finite Galerkin trajectories** from strict initial `W_log(2)` bounds, proves their genuine ODEs on the full common interval, and applies the fixed-core inequality at every time. It does not assume the two trajectories or their analytic bounds.

## Mathematical frontier still open

1. Extract a single subsequence whose trajectories converge uniformly for each frequency, using the previously proved uniform coefficient time Lipschitz bound and compactness of bounded complex three-vectors (diagonal Arzelà–Ascoli).
2. Combine finite-core uniform convergence with the quantitative `200(5/6)^N` remainder to obtain strong `W_log(3/2)` convergence of the zero-extended Galerkin paths, uniformly in time.
3. Pass the *complete* Leray convolution and viscous term using the spare analytic radius and prove the limiting evolution equation; avoid claiming more than the topology of convergence permits.

No claim of subsequence extraction, infinite Fourier Navier–Stokes existence, physical-space regularity, or H³ continuation is made by this module.
