# The shell identity for the existing physical aggregate

Base: 6cd99c00, transport physical first-monomial aggregate to real Schwartz integrals.

## Result

The new module connects h3PathCanonicalFirstMonomialAggregateAt directly to
the shell kernel, assuming a real Schwartz realization f_j of the logged
velocity components at the time in question and physical divergence zero.

Let U_j be the Fourier transform of the complexification of f_j, and put
q=-(p+r). The shell kernel is

    S(p,r) = (p·r)(p·U(q)) |q|² (|r|²-|p|²) Σ_j U_j(p)U_j(r).

The exact physical identity is

    h3PathCanonicalFirstMonomialAggregateAt u t
      = (2π)^7 Im ∫∫ S(p,r) dp dr.

With the admissibility, energy-class and time hypotheses of the existing
interpolation multiplicity theorem, the patch also proves

    thirdOrderInterpolationTransportSum u t
      = 3 (2π)^7 Im ∫∫ S(p,r) dp dr.

The factor two from spatialEnergyPairing cancels the denominator in frequency
exchange. The seven derivatives contribute -i(2π)^7, giving the positive
imaginary-part formula. The interpolation multiplicity is three. No Fourier
normalization or sign is left implicit.

## Bridges supplied

The project already contains real Schwartz complexification and its
compatibility with directional derivatives. Those results are reused.
Integrability of a real Schwartz triple product permits taking its complex
embedding through the integral. This identifies each existing physical
monomial with twice the real part of the complex Schwartz slot.

The five finite coordinate sums are reindexed from j,v,i,k,l to i,k,l,v,j.
The actual physical divergence equation on Point3 is evaluated through the
coordinate identification, transported to the Schwartz derivatives, and then
complexified. This supplies the physical divergence condition of the
previous shell theorem, rather than assuming Fourier incompressibility.

## Remaining analytic boundary

The Schwartz realization is a substantive hypothesis, not a consequence of
arbitrary H3 regularity. This patch does not establish that every preterminal
H3 slice meets it. Extending the identity to the required solution class
needs a regularity or approximation argument that preserves the nonlinear
integrals and incompressibility.

Even on Schwartz fields, the identity is not a critical estimate. The shell
difference has no globally favorable sign. Controlling frequency interactions
with the available energy and dissipation remains the central analytic task.
No finite-time continuation conclusion is asserted.

## Validation

The audit now prints the physical shell identities and their axioms. Source
index, prose-fragment and whitespace checks are run during preparation.
Lean compilation remains pending on the pinned toolchain.
