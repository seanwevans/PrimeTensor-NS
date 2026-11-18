# Strong overlap uniqueness for genuine finite Z³ Galerkin Leray trajectories

Base commit: `cf9eaace7c2889683d619efee5ab2fb52897601c`.

The exact finite-dimensional vector field is polynomial (viscous plus
complete complex Leray convolution) and previously proved real-`C¹`.
It need not be globally Lipschitz. Since the retained coefficient state
space is a finite product of three-dimensional complex Euclidean spaces,
its closed balls are compact. The `C¹` mean-value theorem therefore
provides a finite Lipschitz constant on each fixed closed ball. The constant
is *not* uniform over Galerkin cutoffs; uniformity is unnecessary for ODE
uniqueness.

Mathlib's `ODE_solution_unique_of_mem_Icc_right` then proves that any two
strong paths with the same initial state and values in the same ball agree
on every shared compact interval. We establish this with no reliance on
artificially truncated or modified dynamics.

The stronger theorem applies the already verified cutoff-free moving
analytic barrier separately to both genuine paths. Up to
`(log(2)-log(9/5))/100`, their norms are at most 100 automatically. For
every time before a common endpoint, uniqueness on the compact initial
subinterval proves equality of the two paths there. Hence compatible
Picard solutions cannot branch inside the analytic window.

**Still open:** assemble local solutions by uniqueness into an actual
maximal trajectory and prove the common analytic-horizon existence theorem.
The preceding maximal-endpoint alternative applies to such a trajectory
once existence is constructed. No uniform cutoff-independent Lipschitz
constant is claimed, and no global Navier–Stokes regularity follows.

Verification: Static manifest / registry audit run in staging; Lean needs
compilation with the repository-pinned mathlib toolchain.
