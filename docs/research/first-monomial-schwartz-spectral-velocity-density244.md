# Weighted spectral velocity Schwartz density (244)

Baseline: `1787e859` (2026-10-17).

## New unconditional construction

The repository already proved scalar Schwartz density in the genuine complex
weighted H³ spectral state. Here `DenseRange.piMap` gives a dense subset of
the **three-component spectral velocity state** `H3SpectralVelocityState`.
For any `U` and any positive epsilon, a three-component Schwartz vector
approximates `U` in the exact spectral velocity norm.

Choosing the approximation radius `1/(n+1)` constructs a Schwartz-vector
sequence converging strongly to `U` and hence Cauchy. No approximating
sequence or convergence is assumed.

## Crucial remaining analytic gap

These approximants are Schwartz representatives of **weighted spectral L²**
coordinates. A weighted spectral Schwartz coordinate is not automatically
the weighted Fourier transform of a real physical Schwartz velocity.
To use `completedSchwartzH3FirstMonomial244` on an actual physical H³ slice
we still need:

1. Deweighting and inverse Fourier transform of suitable spectral test data;
2. Preservation of Fourier reality, and the solenoidal constraint if needed;
3. Identification of spectral strong convergence with the actual
   physical-space E₂/E₃ energy convergence;
4. Identification of the completed signed monomial with the physical
   243-slot transport integral.

This checkpoint establishes only the first, unrestricted complex spectral
vector density step. It is not an H³ Navier–Stokes regularity theorem.
