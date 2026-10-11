# Initial uniqueness with right kinetic-energy trace

Base: `327cdeaa` (`derive automatic initial old velocity time measurability`).

New module: `OneComponentInitialRightKineticTraceReduction.lean`.

## Actual improvement

The preceding right-energy-trace criterion requested a finite one-sided limit
of the *full* normalized H³ energy. The old physical L² path needs only the
zeroth-order energy, and the existing `velocityH3L2JetAt_squareEnergy0_eq`
proves its exact identity:

`‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖² = velocityH3Energy0At u t`.

A finite right kinetic-energy limit gives a short initial interval with
`velocityH3Energy0At u t ≤ L+1`, hence the physical old L² ceiling
`Real.sqrt (L+1)`. The selected path is bounded independently by its mild
Picard estimate. Automatic old-velocity time measurability from the preceding
module is reused. The existing integrated-coefficient, arbitrarily-small
residual inequality is restricted to the shorter interval.

New declarations:

- `h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy`
- `h3Audit_initialOldPhysicalHilbert_norm_eq_sqrt_kineticEnergy`
- `h3Audit_initialOldPhysicalHilbert_norm_le_of_kineticCeiling`
- `H3AuditInitialCanonicalRightKineticTraceRelativeEnergyData`
- `h3Audit_initialRightKineticTrace_implies_oldKineticData`
- `h3Audit_initialRightKineticTrace_implies_compactWeakComparisonData`
- `h3Audit_initialRightKineticTrace_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightKineticTrace`

## Still required

An independently justified finite initial kinetic-energy right limit and the
Navier–Stokes old/selected vanishing-residual comparison remain assumptions.
The class of positive-time H³ paths itself need not bound kinetic energy as
time approaches zero. The terminal strong-H³ actual-vorticity endpoint is
independent. This patch does not establish unconditional uniqueness or global
regularity, and Lean must be compiled in the target repository.
