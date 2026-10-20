# Physical identification of the canonical second-order L⁴ trace

Base checkpoint: `52af3e57`. The strong second-jet L⁴ sequence and the physical
second-jet L² sequence are **the same literal Schwartz derivatives**, embedded
into two Lebesgue spaces. Convergence in both spaces implies convergence in
measure to the same a.e. limit (`tendstoInMeasure_ae_unique`). This does NOT
require a finite-volume Euclidean carrier, interpolation into an additional
space, or an independently postulated L⁴ identity.

We obtain, for every one of the 27 ordered derivative slots and each compatible
physical H³ snapshot, almost-everywhere equality between:

* the choice-independent `weightedH3CanonicalSecondJetL4Trace244` and
* `h3ToFourierRealL2 (velocityH3L2JetAt ... (h3JetSlot2 ...))`.

This is the genuine original L² jet's L⁴ representative, on the project's
volume-preserving physical Fourier carrier. The 3-2-2 integrals still need
proof of a.e. representative equality with the integrands used by the old
transport functional, including precise Hölder/integrability transfer. The
3-3-1 gradient pairing must be handled separately.

No NS continuation or regularity conclusion is asserted.
