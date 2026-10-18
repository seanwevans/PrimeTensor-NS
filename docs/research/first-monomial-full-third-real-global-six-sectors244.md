# Global six-sector identity for the actual full-third H³ commutator

Base commit: `6b4b3ade`.

The imaginary part of the actual unphased full-third kernel is absolutely
integrable, Hermitian-even, and supported in the union of twelve *disjoint*
frequency-pair sectors for the small-width hypotheses already established.

The sectors are inverse images of the axis-coordinate sup-norm balls under
`WithLp.ofLp`. Distinct-sector separation occurs in that metric. All
subsequent integrations remain over the actual physical Hilbert product
Lebesgue measure.

Finite additivity (through measurable indicators) decomposes the entire
imaginary-kernel integral into the twelve distinct sector integrals. The
measure-preserving simultaneous reflection `z ↦ (-z.1,-z.2)` pairs six
positive orientations with six reflected ones. The resulting identity is

    fullSchwartzThirdCommutator244 u =
      2 * (2 * Real.pi)^7 * thirdFullPositiveSixSectorIntegral244 ...

The positive scalar does not decide the sector sum's sign. No global
noncancellation, continuation, or Navier–Stokes regularity is claimed.
