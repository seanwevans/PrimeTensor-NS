# The Schwartz first-monomial aggregate and shell cancellation

Base: a6c20f9e, derive Schwartz first-monomial Fourier triad identity.

## Result

FirstMonomialTriadAggregate.lean sums every coordinate slot on the project's
Euclidean Fourier carrier. Let A be the complex integral sum

    A = Σ_{i,k,l,v,j} ∫ (∂i∂k∂l u_j)(∂k∂l u_v)(∂i∂v u_j).

For a Schwartz vector field u, write U for its componentwise Fourier transform.
Put q=-(p+r). Under the explicit Fourier incompressibility condition q·U(q)=0,
the new aggregate identity is

    2 A = (2πi)^7 ∫∫ S(p,r) dp dr,

where the shell kernel is exactly the existing algebraic kernel

    S(p,r) = (p·r)(p·U(q)) |q|² (|r|²-|p|²) Σ_j U_j(p)U_j(r).

Here |q|² means the Euclidean squared norm, represented by the coordinate dot
product. All pairings in the frequency kernel are bilinear, without complex
conjugation. Both the original kernel and S are absolutely integrable.

Taking real parts gives the signed pairing formula

    2 Re A = (2π)^7 Im ∫∫ S(p,r) dp dr.

There is no remaining factor 1/2: exchange of the outer frequencies produces
twice the original integral, exactly matching the factor two in the pairing.

## What is formally connected

The coordinate expansion is identified pointwise with
PrimeTensor.FirstMonomialTriad.amplitudeKernel using the existing
inner_h3FourierAxisDirection theorem. This directly connects the seven-
derivative Fourier identity to the previously proved triad cancellation.

Schwartz slot integrability justifies taking the five finite sums through
the integral. Frequency exchange is Prod.swap on Euclidean product volume,
so no conversion of the integration measure to the coordinate carrier is
needed for this identity.

## What remains

The new aggregate is explicitly a Schwartz aggregate on H3FourierPoint3.
It has not yet been identified with h3PathCanonicalFirstMonomialAggregateAt
for an arbitrary preterminal H3 path. That identification still requires
physical-carrier transport, matching the finite-sum order, and the required
regularity or approximation argument. Fourier incompressibility is an input
here; its derivation from the physical divergence equation remains explicit
work. The existing interpolation multiplicity three can be applied only
after matching the physical aggregate.

The formula preserves the shell difference. It supplies neither a favorable
sign nor the critical estimate needed for continuation. In particular,
absolute convergence of Schwartz kernels does not resolve high-frequency
scale interactions.

## Validation

The patch extends the audit statements and axiom reports and regenerates the
source index. Source-index, fragment, and whitespace checks are run during
preparation. Lean is unavailable in the preparation environment; compilation
with the pinned toolchain remains pending.
