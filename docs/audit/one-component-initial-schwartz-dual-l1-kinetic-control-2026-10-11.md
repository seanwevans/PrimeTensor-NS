# Initial kinetic control from uniformly dominated Schwartz-test weak evolution

Base checkpoint: `836055b4` — derive initial kinetic control from scalar weak FTC.

This patch replaces the requirement of a separate integrable scalar evolution source for **each** test in the **entire** physical Hilbert space by a PDE-facing condition on *three-component Schwartz tests* with a shared norm-proportional temporal source budget.

Given `0 < b`, `0 ≤ M`, and each Schwartz vector `Φ`, the hypothesis supplies a scalar `gΦ` with a true interior two-time increment identity and

\[
\int_0^b |g_\Phi(r)|\,dr\le M\|\Phi\|_{L^2}.
\]

By the basic integral norm estimate, the increment between any two positive times is bounded by `2 M ‖Φ‖`. The repository's **already proved** `denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert` allows this bound to extend to the entire physical vector `L²` Hilbert space. Testing the resulting continuous linear functional against its own Riesz vector then gives

\[
\|u(t)\|_{L^2}\le \|u(b/2)\|_{L^2}+2M,\qquad 0<t<b.
\]

The exact physical kinetic identity converts this to a kinetic-energy ceiling, which closes the cofinal-anchor obligation for the existing conditional initial weak/strong comparison.

## Declarations

- `h3Audit_initialScalarPrimitive_norm_le_totalAbsMass`
- `H3AuditInitialSchwartzDualL1IncrementOn`
- `h3Audit_initialSchwartzDualL1_pairingIncrement_le`
- `h3Audit_initialSchwartzDense_pairingBound_implies_normBound`
- `h3Audit_initialSchwartzDualL1_uniformOldL2`
- `H3AuditInitialCanonicalSchwartzDualL1RelativeEnergyData`
- `h3Audit_initialSchwartzDualL1_implies_kineticAnchorData`
- `h3Audit_initialSchwartzDualL1_implies_compactWeakComparisonData`
- `h3Audit_initialSchwartzDualL1_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSchwartzDualL1`

## Status and non-circularity

The **uniform dual `L¹` budget** is a separate PDE analytic hypothesis; scalar FTC against each individual Schwartz test without a common norm-proportional majorant is *not* sufficient for a uniform physical `L²` bound. The initial Fourier datum and epsilon-vanishing old/selected relative-energy comparison remain assumed. The terminal actual-vorticity strong-`H³` endpoint is also assumed. No unconditional 3D Navier–Stokes regularity theorem follows.

Lean compilation and project audit must be run locally before merging. No `sorry` or `admit` is used.
