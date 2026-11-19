# Hermitian reflection on the exact Z³ Fourier lattice

**Base commit:** `6357bd8ad2b38c081cfbd308fdda1ed32704116a`

## Mathematical result

The preceding module constructs an actual local solenoidal complex Fourier
Navier–Stokes flow using genuine Galerkin ODE trajectories. A real-valued
periodic velocity requires the additional Fourier reality condition

\[
\widehat u(-n)=\overline{\widehat u(n)}\qquad(n\in\mathbb Z^3).
\]

The new module defines componentwise conjugation on the *actual*
`EuclideanSpace ℂ (Fin 3)` velocity, proving it is a real-linear,
continuous, isometric involution. Frequency negation is compatible with
complex Fourier frequency, Laplacian norm, lattice l1 degree, and every
analytic Wiener weight.

The canonical fixed Galerkin cubes are closed under `n ↦ -n`; hence a
Hermitian infinite initial state restricts to compatible finite Hermitian
coefficients. The zero-extension of a Hermitian state on a symmetric cutoff
is Hermitian on the entire integer lattice, including absent frequencies.

The Hermitian average

\[
(Hu)(n)=\tfrac12\big(u(n)+\overline{u(-n)}\big)
\]

is exactly Hermitian and obeys the sharp pointwise cost

\[
\|(Hu)(n)\|_2 \le
  \tfrac12\big(\|u(n)\|_2+\|u(-n)\|_2\big).
\]

Finally, a uniform-in-time coefficientwise limit of Hermitian finite Fourier
fields remains Hermitian, with no assumed infinite-dimensional derivative.
A specialized theorem packages that fact for actual finite Galerkin states
and symmetric Fourier supports.

## What is not yet proved

The *nonlinear-equivariance* identity

\[
\mathcal B(\overline{u(-\cdot)},\overline{u(-\cdot)})(n)
  =\overline{\mathcal B(u,u)(-n)}
\]

has not been discharged here for the exact complex Leray projector.
The next step is to prove conjugation equivariance of that projector and
the collision-sensitive ordered convolution, then invoke finite-ODE
uniqueness to propagate Hermitian symmetry along the constructed Galerkin
trajectories. The limit-closure theorem in this package will then give
Hermitian reality of the infinite solution without imposing it as a premise.
No global-in-time, physical R³, or Clay continuation result is claimed.
