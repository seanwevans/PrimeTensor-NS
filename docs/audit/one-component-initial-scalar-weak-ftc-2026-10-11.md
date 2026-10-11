# Initial kinetic control from full-L² scalar weak FTC

Parent: `3b200a8a01fb0e6eaaab8988d8fc9dfa427c169d`

## Hypothesis reduction

The previous `OneComponentInitialBochnerDerivativeKineticControl` used an
`L¹((0,b); L²(ℝ³)^3)` strong Bochner derivative of the actual old velocity.
This module instead assumes *separately for every fixed full physical L² test*
`ψ` an integrable scalar source `gψ` and the exact, interior two-time weak
increment identity:

`⟪u(t),ψ⟫ - ⟪u(s),ψ⟫ = ∫ s..t, gψ(r) dr`, for `0 < s,t < b`.

The scalar source may depend on `ψ`; it need not arise from a common
physical `L²`-valued time derivative. Integrability is required all the
way down to zero **for each scalar test**, not just locally away from zero.

## New declarations

- `h3Audit_initialScalarIntegrableIncrements_exists_rightLimit`
- `h3Audit_initialPositiveSequence_cofinal_of_rightTendsto`
- `H3AuditInitialFullL2ScalarWeakFTCOn`
- `h3Audit_initialFullL2ScalarWeakFTC_pairingsBoundedOnSequence`
- `h3Audit_initialFullL2ScalarWeakFTC_kineticAnchors`
- `H3AuditInitialCanonicalScalarWeakFTCRelativeEnergyData`
- `h3Audit_initialScalarWeakFTC_implies_pointwisePairingData`
- `h3Audit_initialScalarWeakFTC_implies_compactWeakComparisonData`
- `h3Audit_initialScalarWeakFTC_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialScalarWeakFTC`

## Proof chain

1. An interior scalar FTC with one `L¹` source gives a finite scalar right limit
   using a single interior anchor and the absolutely continuous primitive.
2. Composition with a sequence `τ n → 0+` yields bounded weak-pairing sequences
   against every full physical `L²` test.
3. Banach–Steinhaus (already established in the parent chain) gives a common
   physical `L²` norm ceiling for the sampled actual old velocity.
4. The exact old-velocity kinetic identity plus full positive-time kinetic
   antitonicity extend the bound to all initial positive times.
5. The previously proved relative-energy criterion yields compact weak-test
   equality and then the conditional physical trace conclusions.

## Remaining conditions

The scalar weak evolution is an explicit PDE-side assumption. Its derivation
from compactly supported distributional Navier–Stokes test equations for **all**
physical L² tests, with individual `L¹` source control near zero, is not yet
proved. Convergence of compact test pairings alone does not provide it.

The independent epsilon-vanishing old/selected nonlinear relative-energy
comparison and the strong-H³ actual-vorticity terminal condition also remain.
No unconditional Navier–Stokes regularity claim is made.
