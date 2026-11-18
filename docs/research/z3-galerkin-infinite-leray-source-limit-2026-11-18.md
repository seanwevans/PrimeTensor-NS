# Infinite exact Leray source: weighted Fourier completion

**Parent:** `2b6e6016a385ec3eb8612de8972b2862b2eed19d`

The previously constructed Z³ Galerkin trajectories have (i) uniform closed-time
high-radius Wiener mass at most 100; (ii) strong uniform-time convergence in
`W_log(3/2)`; and (iii) an exact cutoff-independent Lipschitz estimate for the
**complete projected complex Leray convolution** over arbitrary finite output
sets, not just modes retained by the finite ODE.

This module performs the missing infinite *source completion* rather than
assuming that all Fourier outputs already have a limit.

## New results

1. `thirdFullThreeBand_z3GalerkinQuadratic_allOutputs50000_244`: for
   **every** finite output set `A`, the full quadratic source obeys
   `W_log(5/4)^A(Q_S(u,u)) <= 50000`. Its proof uses the existing
   convolution `W_r D_r` bound, radius monotonicity, the fivefold
   one-derivative analytic reserve and the 100 high-radius ball. No
   output-cardinality factor or projection to retained outputs occurs.
2. `thirdFullThreeBand_z3Galerkin_sourceModeCauchy244`: the uniform
   all-finite-output source Cauchy property yields a genuine Cauchy
   sequence at every lattice output and time.
3. `thirdFullThreeBand_z3Galerkin_uniformSourceCompletion244`: completeness
   of the complex three-coordinate band constructs the infinite source
   `Q(t,n)`; it proves `sum_n (5/4)^degree(n)*norm(Q(t,n)) <= 50000` and
   uniform convergence of the finite sources in that **full infinite
   weighted sum**. No existence of limit coefficients or infinite
   summability is assumed.
4. `thirdFullThreeBand_z3Galerkin_actualInfiniteSourceLimit244`: instantiates
   the completion with actual full quadratic Leray sources from arbitrary
   nonnested cutoff-indexed Galerkin paths.
5. `thirdFullThreeBand_z3Galerkin_exists_constructedInfiniteSourceLimit244`:
   jointly constructs the genuine finite ODE solutions, the single Fourier
   subsequence and its infinite source completion from the strict
   `W_log 2 < 100` initial ball.

## Scope and remaining mathematical barriers

The constructed source is **the uniform-in-time W_log(5/4) limit of the exact
finite ordered-pair Leray sums**. This is more than a finite-core Cauchy
estimate, but does **not yet** identify the limit with an independently
constructed, absolutely convergent ordered-pair convolution
`sum' p, -i P_n[((n-p) dot u_p) u_(n-p)]`.

The identity with that infinite convolution requires explicit absolute
summability and a fixed-output dominated-support exhaustion argument.
Passing the finite ODE's time integral to the limit additionally requires
cutoffs eventually containing each fixed output mode and compatible
converging initial data. Arbitrary nonnested cutoffs need not exhaust the
lattice, so **no** infinite-dimensional Navier--Stokes equation follows
without those hypotheses. The current theorem asserts neither an infinite
PDE nor global regularity.

All constants are independent of the cutoff cardinality. Lean compilation
must be carried out against the pinned Lake/mathlib environment.
