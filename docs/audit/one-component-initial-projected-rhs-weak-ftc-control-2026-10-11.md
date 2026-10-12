# Initial projected-RHS weak-FTC control

Base checkpoint: `a7b09bf9` — derive initial kinetic control from Schwartz dual L1 evolution.

## Reduction

The preceding Schwartz criterion assumed, for each physical three-component Schwartz test `Φ`, a scalar integrable source `g_Φ` obeying a common dual bound:

    ∫₀ᵇ |g_Φ(s)| ds ≤ M ‖Φ‖_(L²).

This module generates those test-indexed scalar sources from **one** physical Hilbert-valued projected momentum source `G : ℝ → H3PhysicalRealFinVectorL2Hilbert`, assuming the two distinct PDE-facing facts:

1. The *old physical velocity* satisfies its Schwartz weak momentum increment equation between every two **strictly positive** initial times, with RHS `<G(s), Φ>`.
2. `G` is Bochner-integrable on `(0,b)`, with `∫₀ᵇ ‖G(s)‖ ds ≤ M`.

Bounded linear functional composition proves scalar interval integrability. Pointwise Cauchy–Schwarz and monotonicity of the interval integral give the common dual bound:

    ∫₀ᵇ |<G(s), Φ>| ds ≤ ‖Φ‖ ∫₀ᵇ ‖G(s)‖ ds ≤ M ‖Φ‖.

Schwartz density and the previous kinetic monotonicity/relative-energy machinery now yield conditional initial compact weak-test uniqueness, actual initial physical zero-jet L² and upper H³ traces, and (with independent terminal-vorticity data) two transverse full-time intrinsic Sobolev estimates.

## What is *not* proved

- The existential `G` is **not yet identified** with the literal projected Navier–Stokes momentum RHS `Δu - P div(u⊗u)` on the entire initial interval.
- No initial `L¹_t L²_x` estimate of that actual RHS is obtained from open-positive-time H³ admissibility alone.
- No old/selected epsilon-vanishing relative-energy residual is derived; it remains an independent assumption.
- No terminal strong H³ actual-vorticity endpoint, unconditional 3D Navier–Stokes regularity, or smooth continuation is established.

## Main declarations

- `h3Audit_initialProjectedRHS_scalarPairing_intervalIntegrable`
- `h3Audit_initialProjectedRHS_scalarMass_le`
- `h3Audit_initialProjectedRHS_implies_schwartzDualL1`
- `H3AuditInitialCanonicalProjectedRHSWeakFTCRelativeEnergyData`
- `h3Audit_initialProjectedRHS_implies_schwartzDualL1Data`
- `h3Audit_initialProjectedRHS_implies_compactWeakComparisonData`
- `h3Audit_initialProjectedRHS_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialProjectedRHS`
