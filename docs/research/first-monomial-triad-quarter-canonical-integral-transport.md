# Canonical-axis transport of the signed six-order Fourier integral

Base checkpoint: `e1ac277c` (real Schwartz velocity on canonical H3 axes).

The actual quarter-scale velocity has three real Schwartz components whose
complexified Fourier transforms are the reindexed Hermitian, solenoidal
noncancelling packet. This module proves:

- the axis-to-Fin coordinate permutation preserves product volume;
- the `H3FourierPoint3 → Fin 3 → ℝ` carrier map preserves volume;
- its product map on two independent momentum variables preserves volume;
- the complete six-order Fourier coefficient is invariant under simultaneous
  frequency/polarization coordinate reindexing;
- the complexified real Schwartz velocity's six-order kernel equals the
  original packet's kernel after reindexing, retaining `(2πi)^7`;
- the integral of the physically phased six-order coefficient on the canonical
  carrier is strictly negative for a proved positive packet width.

**Next:** use the existing `h3SchwartzTriadSixOrderKernel_integral` and physical
Schwartz first-monomial identity to identify this negativity with the actual
real-space spatial monomial functional. Do not infer a Navier–Stokes blowup or
continuation theorem from the signed noncancellation example.
