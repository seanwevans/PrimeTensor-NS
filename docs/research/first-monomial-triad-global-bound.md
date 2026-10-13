# Global shell bound and physical interpolation estimate

Base: 542ddfab, linear separation gains for both outer-frequency regions.

## Exact assembly

The two regions P<=R and R<=P cover every triad. Their overlap is P=R,
where the shell factor R²-P² vanishes pointwise. Thus the full shell kernel
is exactly the sum of the two restricted kernels at eps=1. No assertion
that the overlap has measure zero is needed.

Each restricted integral has norm at most 2 E3 M1. The triangle inequality
gives the global estimate

    |integral S| <= 4 E3 M1,
    E3 = integral (|p|³ |U(p)|_2)²,
    M1 = integral |q| |U(q)|_2.

The new named quantities use the project's Euclidean Fourier carrier and
include no powers of 2 pi. All polynomial moment finiteness follows from
Schwartz data as already proved.

## Actual physical quantities

For a real Schwartz realization of the logged physical velocity at time t,
with physical divergence zero, the established shell identity now implies

    |h3PathCanonicalFirstMonomialAggregateAt u t|
      <= 4 (2 pi)^7 E3 M1.

Under the existing admissibility, energy-class and interior-time hypotheses,
the exact interpolation multiplicity three yields

    |thirdOrderInterpolationTransportSum u t|
      <= 12 (2 pi)^7 E3 M1.

Here U is the Fourier transform of the complexified real Schwartz velocity.
The constants include the existing physical pairing factor and Fourier
phase; the proof reuses the physical identity rather than inferring them
from a dimensional argument.

## Mathematical status

All frequency regions now have a global E3 M1 bound. The earlier estimates
retain additional small coefficients on separated regions: quadratic for
a low middle frequency and linear for a low outer frequency. Setting eps=1
assembles a global estimate but loses those small coefficients.

This is not a critical absorption estimate. Comparable-frequency triads
have not acquired an additional favorable sign or smallness factor, and
finite Schwartz moments are not uniform bounds along a potential singular
time sequence. The actual next question is whether the signed comparable
interaction has usable structure beyond this absolute estimate, or whether
the PDE provides sufficient control of the resulting energy-moment product.
The explicit Schwartz realization still limits the physical theorem's scope.

## Checks

Source index, fragment consistency and whitespace checks run before packaging.
Lean compilation and the theorem audit remain pending on the pinned local
toolchain. No axioms or sorry declarations are introduced.
