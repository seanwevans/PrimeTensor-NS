# Global homogeneous Ḣ^(3/2) time measurability — 2026-10-10

Base commit: `e73b5be3`.

The previously proved strict local windows contain each interior physical time.
Pulling the continuous elapsed-time function back through the affine coordinate
`x ↦ x - t` establishes continuity at that time. Therefore the exact selected
homogeneous Ḣ^(3/2) square density is continuous on `(0,T)`.

Its definition is identically zero outside `(0,T)`. A measurable piecewise
extension therefore gives a globally Borel-measurable real-time function.

This removes the explicit time-measurability (and stronger state-measurability)
assumptions in the earlier homogeneous Ḣ^(3/2) endpoint-integrability
statements. The conclusion remains **conditional** on the existing physical
curl-component endpoint and H³ energy-class assumptions; neither Navier–Stokes
global regularity nor an external Liu–Zhang continuation bridge is proved.

Files: `OneComponentGlobalTimeMeasurability.lean`; registration added to
`PrimeTensor.lean` and `tools/audit/Contracts.lean` by the run script.
