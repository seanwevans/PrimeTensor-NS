# Initial actual physical projected RHS dominated by H³ energy

Base checkpoint: `4676a452` — derive initial kinetic trace from physical projected RHS.

## Added module

`PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialEnergyDominatedProjectedRHS.lean`

The prior checkpoint required independent Bochner `IntervalIntegrable` of the *actual*
physical source `G = D - N` over `(0,b)`. The current patch derives that requirement
from a single scalar premise:

`IntervalIntegrable (velocityH3EnergyAt u) volume 0 b`.

This uses existing actual reconstructed Fourier-source norm bounds, and the
previous global positive-time physical RHS continuity theorem for automatic
`AEStronglyMeasurable` on `(0,b]`. It does **not** postulate separate source
measurability or pointwise estimates.

The precise integral bound is

`∫₀ᵇ ‖D(t)-N(t)‖ dt ≤ (3 + C_L) ∫₀ᵇ velocityH3EnergyAt u t dt`

where `C_L = h3AuditInitialLerayEnergyCoefficient`.

The bridge then uses the preceding strong-derivative/kinetic-right-limit
theorems to construct the finite physical L² and kinetic right traces, and
feeds the existing compact weak comparison and physical initial H³ upper-trace
results without assuming an independent source integral.

## New declarations

- `h3Audit_initialActualProjectedRHS_integrable_and_mass_of_h3Energy`
- `h3Audit_initialOldJointEnergyRHS_exists_physicalHilbertRightLimit`
- `h3Audit_initialOldJointEnergyRHS_kineticRightLimit`
- `H3AuditInitialCanonicalEnergyDominatedRHSRelativeEnergyData`
- `h3Audit_initialEnergyDominatedRHS_implies_projectedRHSData`
- `h3Audit_initialEnergyDominatedRHS_implies_rightKineticData`
- `h3Audit_initialEnergyDominatedRHS_implies_compactWeakComparisonData`
- `h3Audit_initialEnergyDominatedRHS_implies_physicalZeroJetAndEnergyUpper`

## Remaining independent obligations

The scalar `L¹(0,b)` H³-energy bound itself remains independent of bare
positive-time H³ path admissibility. The old physical velocity temporal
derivative's joint spacetime continuity is also still an additional
regularity input. Initial old/selected relative-energy residual decay and
the terminal actual-vorticity strong-H³ endpoint remain separate hypotheses.

The patch does not prove unconditional Navier–Stokes global regularity.

## Validation

Lean and lake are not present in this artifact environment. Compile the module
and the project in the user's Rocky Linux repository before committing.
