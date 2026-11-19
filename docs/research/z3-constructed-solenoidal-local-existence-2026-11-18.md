# Local projected Fourier Navier–Stokes existence with propagated solenoidality

**Parent HEAD:** `0a272aa71799364fc71054dce4ddac72e2040c10`

## Mathematical advance

The preceding existence theorem constructs genuine complex Fourier coefficient
paths on the integer lattice, with a common cutoff-independent lifespan,
prescribed analytic initial data, and the full absolutely convergent Leray
convolution in a coefficientwise integral equation. Its solenoidal variant
still left the **velocity** longitudinal constraint unproved at positive times.
The immediately preceding rigidity theorem did prove preservation, but assumed
classical time derivatives of the infinite flow.

This module removes that derivative assumption for the **constructed** flow.
It exploits a stronger, already available structure: the actual finite
Galerkin trajectories and their one common Arzelà subsequence.

At each retained frequency n and finite cutoff k,

\[
  w_{k,n}(t) = \langle \xi_n, u_{k,n}(t)\rangle_{\mathbb C},
  \qquad
  w'_{k,n}(t) = -\mu\|\xi_n\|_2^2 w_{k,n}(t).
\]

All quadratic terms vanish identically under the frequency pairing, because
the *complete* collision-sensitive Galerkin source is Leray-projected at its
output. Projecting the initial field makes every retained initial coefficient
transverse, so `LongitudinalHeat_scalarRigidity244` and Grönwall show
`w_{k,n}(t)=0` on the entire closed common horizon, even if `mu=0`.

For every fixed lattice frequency n, cutoff exhaustion ensures n is retained
eventually along the same strictly increasing Arzelà subsequence. Uniform
mode convergence and continuity of the frequency pairing then give

\[
  \langle\xi_n,g_n(t)\rangle_{\mathbb C}=0
  \qquad\text{for every }n\in\mathbb Z^3
  \text{ and every }t\text{ in the common local interval}.
\]

The strengthened existence theorem reproduces the actual Galerkin construction
and uses that **same** subsequence for high-Wiener bounds, uniform source
completion, identification with the infinite ordered Leray series, and the
coefficientwise time-integral equation. There is no separate, unconnected
existence argument for the transverse limit.

## Declarations

- `thirdFullThreeBand_z3GalerkinFiniteODE_transversePreserved244`: the exact finite ODE preserves the transverse constraint, with no assumption about future transverse coefficients.
- `thirdFullThreeBand_z3Galerkin_uniformLimit_transverse244`: an exhaustive uniformly convergent Fourier subsequence inherits the closed complex frequency constraint.
- `thirdFullThreeBand_z3ProjectedInitial_solenoidalLocalExistence244`: an actual infinite local Fourier Navier–Stokes solution with projected initial trace, analytic 9/5 Wiener ceiling 100, source 5/4 Wiener ceiling 50000, exact infinite ordered Leray integral evolution, and transverse velocity for every time and frequency.
- `thirdFullThreeBand_z3FixedCubes_solenoidalLocalExistence244`: specialized concrete family of exhaustive integer Fourier cubes, without an abstract cutoff-exhaustion premise.

## Scope and next frontier

This establishes local **complex periodic Fourier** solenoidality for the
constructed solution; it does not assert Hermitian Fourier symmetry or
real-valued physical-space velocity. Hermitian symmetry must be propagated
through the same finite Galerkin construction. It does not establish global
three-dimensional Navier–Stokes regularity or physical R³ H³ continuation.
