# Physical Fourier identification for one-component endpoint (2026-10-10)

Base: `74155325` (`package homogeneous H3/2 Fourier time L2 criterion`).

## The actual velocity snapshot, not a surrogate

The project's canonical spectral encoder stores `W₃ · û_j`, where `û_j` is the
Fourier transform of the zeroth-order `H³L²` velocity jet at a strict time.
The already-proved encoder/deweighter round-trip
`h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq` identifies the
raw Fourier amplitude exactly with `velocityH3BaseFourierAt` in `L²`.

`OneComponentPhysicalFourierIdentification.lean` specializes this result to
the actual complementary component selected by a physical curl-gradient pair.
It proves a.e. equality and equality of the homogeneous `Ḣ^(3/2)` weighted
spatial Fourier integrals. The zero-extended physical Fourier square density
and corresponding seminorm agree at all times with the previously audited
density and seminorm. Therefore both selected physical Fourier seminorms are
in `L²` time on the same terminal interval under the existing endpoint and
energy-class hypotheses.

## Explicit boundary

This identifies the actual physical *Fourier transform* and normalization.
It is not yet a formal equivalence with an independently defined physical
homogeneous Sobolev function space (e.g. a distributional Fourier definition
at the level of the publication), and it does not import or reprove the
Liu--Zhang continuation theorem or its exact local-strong-solution class.
No universal H³ tail estimate or global regularity is claimed.
