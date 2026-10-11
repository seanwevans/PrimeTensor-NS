# Initial scalar relative energy: positive-time continuity and right trace

Base commit: `3ae4d673` (`refresh Lean source index for CI audit`).

This change factors the initial scalar-energy continuity premise in the epsilon-residual comparison into two PDE-facing inputs:

1. `ContinuousOn e (Set.Ioc 0 b)`: continuity for strictly positive time up to the right endpoint.
2. `Tendsto e (𝓝[>] 0) (𝓝 0)`: a real right-hand zero energy trace at initial physical time.

The mathematical content of the endpoint requirement is **not** removed. The scalar relative energy at `t = 0` is a deliberately zero-anchored value and alone implies no right limit. Existing epsilon-integrated residual comparisons remain separately required.

The main new theorem `h3Audit_initialScalarClosedContinuous_of_positiveAndRightTrace` proves closed interval continuity from these two hypotheses using an epsilon-delta argument. The theorem `h3Audit_initialScalarRightZero_of_strongDifferenceRightZero` provides a sufficient condition in terms of strong right convergence of the actual physical Hilbert-space comparison.

`H3AuditInitialCanonicalEpsilonResidualRightTraceData` packages the resulting alternative interface. It maps into the previously established epsilon-residual criterion, then into physical compact weak-test agreement, initial L²/H³ trace, and the conditional full-time transverse homogeneous H^(3/2) conclusion.

This is a dependency/interface reduction, **not** a derivation of zero-time matching from open-time Navier–Stokes assumptions, nor a proof of the PDE epsilon-residual estimate. The independent terminal strong-H³ actual-vorticity condition remains explicitly required.
