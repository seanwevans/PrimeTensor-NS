# Compact-test signed PDE temporal oscillation and physical distributions

Base: `00970022` — derive physical momentum distributions from interior signed PDE domination.

The previous result required a locally uniform bound for the full signed physical
momentum `Δu_j − (u · ∇)u_j − ∂_j p` over all points in the compact support of
each solenoidal weak test. The repo already proves that this expression is
bounded on the *fixed* compact support at every fixed positive time, by spatial
continuity of the classical temporal derivative. The missing information is
uniformity over a time neighborhood.

The new predicate `h3PreterminalSignedMomentumUniformTimeOscillationOnElapsed244`
requires only a uniform temporal increment modulus relative to each fixed
snapshot, on each test support. At ε=1, the triangle inequality combines the
snapshot bound `C0` with the increment bound `1` to give `C0+1`. This proves the
existing `h3PreterminalSignedMomentumCompactBoundOnElapsed244` predicate.

On a *straddling* canonical restart interval, the new signed bound transfers to
weak evolution, to scalar weak FTC, to actual strong physical L² differentiation,
and finally to the exact compact-time distributional momentum equation. If the
physical Hilbert FTC defect is nonzero, some interior time lacks such a
straddling uniform-oscillation witness.

**Analytic boundary:** The spatial fixed-time bound is proved from the classical
PDE, but the uniform temporal oscillation is an explicit analytic premise.
Neither bare H³ path admissibility nor separate continuity nor strong L²
continuity of the projected RHS is used to assert uniform spatial temporal
oscillation. The new theorem is conditional, not a Navier–Stokes regularity
or continuation theorem.
