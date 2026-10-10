# Real-valued physical fractional L² realization after `28d940ef`

The existing physical Fourier half-derivative bridge packages the exact
`(2π|ξ|)^(3/2)` multiplier in complex `L²`. This module proves that for
**actual real** logged-velocity inputs, the homogeneous multiplier respects
a.e. Hermitian reflection symmetry. The inverse Fourier transform is
therefore the complexification of a real-valued physical `L²` class.

The proof uses the existing `velocityH3SpectralScalarAt_rawHermitian`,
`h3SpectralScalarRawFourier_hermitian_ae`, and
`h3FourierL2Hermitian_fourierInv_eq_complexify_real` theorems; none of those
analytic interfaces is replaced by a fresh hypothesis. The real derivative
has the exact same norm as the complex derivative and the original Ḣ³ᐟ²
Fourier square energy. One physical curl-component endpoint therefore
controls two transverse *real* fractional derivative norms in `L²_t` on a
common late interval.

This closes the reality/complexification issue for the project's internal
L² fractional derivative. It does **not** formalize an independent
homogeneous Sobolev distributional-space equivalence, establish compatibility
with every strong-solution assumption of the cited Liu--Zhang theorem, or
import the theorem's continuation conclusion. The strong endpoint is still
an explicit antecedent, not a universally established property.
