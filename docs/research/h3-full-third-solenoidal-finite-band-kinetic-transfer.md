# Finite-band weighted H³ from physical kinetic Fourier L²

Parent commit: c21747f911344c49054f8e216f3393955c027fe8.

This checkpoint proves a genuine finite-band multiplier estimate for the exact
native H³ weight W₃² = 1 + q + q² + q³, q=(2π)²|ξ|².

For ρ=R+1, W₃(ξ) ≤ C_R := √(1+ρ²+ρ⁴+ρ⁶) on the *strict* low band
2π|ξ|<ρ. Thus

    ‖Q_R(U-V)‖_{H³ spectral} ≤ C_R ‖raw(U)-raw(V)‖_{L² Fourier vector}.

The proof works with actual L² equivalence classes, uses the project's
canonical deweight/reweight theorem and the exact complement of the earlier
high-radial cutoff, and does not assume pointwise Schwartz regularity.

### Precise frontier

The accompanying physical transfer identifies `raw(U(t))` with the physical zeroth-order
velocity via the existing `h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2`
and Plancherel. That establishes fixed-band H³ Cauchy from ordinary kinetic
L² terminal Cauchy, and yields a terminal H³ trace or high-frequency escape
alternative when the corresponding high-radial tightness/nonconvergence
conditions are supplied. The physical PDE projected-momentum FTC identity is still
an explicit prerequisite when attempting to get kinetic terminal increments
from the Bochner-L¹ projected source. Source integrability **alone** does not
identify a derivative of the physical velocity. No terminal H³ continuation
or full-time Fourier-flux bound follows from the present estimates.
