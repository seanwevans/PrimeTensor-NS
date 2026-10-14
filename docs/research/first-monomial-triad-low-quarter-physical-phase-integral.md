# Full six-order integral with the physical seven-derivative Fourier phase

Base commit: `491ab423` — prove positive full six-order signed Fourier integral.

The new module `FirstMonomialTriadLowQuarterPhysicalPhaseIntegral.lean` proves that the
actual seven-derivative Fourier multiplier is `(2 * π * I)^7 = -(2 * π)^7 * I`.
The previously positive full six-order integral therefore gives a strictly **negative**
full six-dimensional Fourier integral after inserting this physical multiplier.
There is no extra Fourier normalization factor in this step.

The proof also connects the windowed, divergence-free polarization field to the
existing exact three-cyclic-shell identity **pointwise**, and establishes
integrability of the physically phased kernel.

**Scope:** This proves a Fourier symbol integral identity and its strict sign.
It does not yet realize the constructed Hermitian vector-valued Fourier Schwartz
map as the Fourier transform of a real vector Schwartz field on the project's
`H3FourierPoint3` / `Point3` carriers, nor does it transfer the formula to the
path aggregate `h3PathCanonicalFirstMonomialAggregateAt`. Those require a carrier
identification, Fourier inversion/reality, and the existing physical first-
monomial transport/cyclic integration theorems.
