# Full-third Schwartz Fourier: five-axis physical-density reindexing

**Pinned baseline:** `7df9085e` — prove unconditional Schwartz integrability of full H3 ordered radial flux.

## The mathematics

The existing `thirdFullSchwartzOrderedSevenKernel244` is an absolutely
integrable complex Schwartz Fourier kernel identified pointwise with the
*corrected ordered* physical polynomial. Its normalized integral is not yet
the physical H3 commutator until we match all four original gradient
placements, the threefold interpolation and the seventh-order Fourier phase.

This patch proves the nontrivial FINITE-INDEX part of that remaining bridge.
For each momentum pair z=(p,r), use the genuine Schwartz transforms of ONE
arbitrary three-component complex Schwartz field. Let G1,...,G4 be the four
original 3+3+1 gradients in their original velocity-component placements and
I the 3+2+2 first-monomial kernel. Define

  H(u,z) = sum_{j,m,i,k,l} [G1 + G2 + G3 + G4 + 3 I].

The derivative-index contractions are not interchangeable at any fixed
`(i,k,l)`. Nevertheless, for arbitrary complex spectral amplitudes,

  G3(i,k,l) = G2(i,l,k),
  G4(i,k,l) = G2(l,k,i).

Thus, after summing all three derivative directions, `G2+G3+G4`
becomes `3*G2`. The interpolation sum can be cyclically permuted to the
ordered kernel's exact `(l,i,k)` direction convention. This gives the
pointwise identity

  H(u,z) = thirdFullSchwartzOrderedSevenKernel244(u,z)
         = thirdFullSchwartzComplexOrderedKernel244(u,z).

The Lean theorem proves it with the physical Axis Depth.three finite sums,
not by assuming permutation-invariance of each individual kernel.

Absolute integrability follows from the committed ordered-kernel theorem.
Combining with the already-proved measure-preserving six-permutation identity
and the exact complex sixth-power flux gives, for any divergence-free complex
Schwartz velocity,

  ∫_{R^6} sixthPowerFlux(u,z) dz = 6 ∫_{R^6} H(u,z) dz.

There is also an unconditional version for any REAL Schwartz velocity with
`lowNormalRealSchwartz_Point3Solenoidal`, using the existing physical
Fourier-divergence bridge.

## What remains

The module has *not yet proved* that the original
`fullThirdSchwartzFourierCoefficient244 f` equals
`2*(2*pi*i)^7 * ∫ H(complexify f,z) dz`. That requires exchanging the
five finite sums with the original four Fourier gradient integrals, matching
the cyclic interpolation sum and its physical factor six, and applying the
already-established odd seventh-order Fourier phase. No PDE-time estimate or
regularity claim follows from this algebraic identity.

The direct next acceptance test is the exact unrestricted physical formula

  fullSchwartzThirdCommutator244(f)
    = (2*pi)^7/3 * Im ∫_{R^6} sixthPowerFlux(complexify f,z) dz

for real physically solenoidal Schwartz f, without new analytic premises.

## Validation

The archive and idempotent registrar are checked locally. The Lean compiler
and project packages are not available in the assistant container, so the
proof must be checked by the repository's pinned `lake env lean` toolchain.
