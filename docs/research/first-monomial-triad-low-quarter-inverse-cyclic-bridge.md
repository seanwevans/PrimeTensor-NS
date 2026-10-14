# Quarter-scale inverse Fourier and cyclic-shell bridge

Base: `712f72ca` — transfer six-order noncancellation to physical Fourier phase.

This module closes two intermediate statements without yet asserting an
unproved physical-space identification.

1. The existing vector Fourier Schwartz packet has three scalar Schwartz
   components. After precomposition with `EuclideanSpace.equiv ℝ (Fin 3)`, each has a Schwartz inverse Fourier transform on the Hilbert carrier `EuclideanSpace ℝ (Fin 3)`. Fourier
   inversion recovers the **entire** weighted Fourier polarization pointwise;
   Fourier solenoidality and Hermitian symmetry follow directly from the
   packet theorems, without hidden realization assumptions.
2. For the same weighted packet, the pointwise identity between the complete
   six-order coefficient and three cyclic shell terms transfers the physical
   multiplier `(2 * pi * I)^7` exactly. The full real integral of the cyclic
   shell sum is strictly **negative** at a suitable width.

What is **not** yet concluded: The complex inverse-Fourier Schwartz components
are real valued; identifying `Fin 3` with the canonical `Axis Depth.three`,
the Euclidean carrier with `H3FourierPoint3`, or the physical `Point3`
first-monomial aggregate; nor any PDE regularity or blowup assertion.

Next: prove Hermitian-to-real converse for the scalar inverse Fourier
components, then the exact `Fin 3` / `Axis Depth.three` / `WithLp` transport,
and instantiate the already established physical Schwartz aggregate identity.

## Carrier correction after first Lean run

The initial version attempted `𝓕⁻` on `𝓢(Fin 3 → ℝ, ℂ)`.
The default function-space norm is not the Euclidean `ℓ²` inner-product
space required by mathlib's Fourier instances. The repaired construction
transports the Schwartz scalar amplitude by the standard continuous linear
equivalence from `EuclideanSpace ℝ (Fin 3)` to `Fin 3 → ℝ` and performs
inverse Fourier transformation on the Euclidean carrier. The recovery,
divergence, and Hermitian statements now evaluate the original frequencies
through `WithLp.ofLp` explicitly.

No assertion that the Euclidean inverse is real-valued is introduced.
