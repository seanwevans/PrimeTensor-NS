# Initial relative energy with continuous integrated coefficients

Base checkpoint: `d3066958` — derive initial uniqueness with time-integrated coefficients.

## Analytic change

The previous criterion assumes separate interval integrability of the product
`κ(s) * e(s)` even when the coefficient is regular. Here the product's
integrability is proved from `IntervalIntegrable e volume 0 b` and
`ContinuousOn κ (Set.Icc 0 b)` (with `0 ≤ b`) using mathlib's
`IntervalIntegrable.continuousOn_mul` and `Set.uIcc_of_le`.

The coefficient may be signed, but still must satisfy the uniform upper
bound `κ(s) ≤ K`. The physical initial comparison energy is nonnegative by
construction. Arbitrarily small integrated absolute residuals remain the
separate PDE-side requirement; the scalar right-zero trace is derived by the
preceding integrable-energy argument, not assumed.

## New declarations

- `h3Audit_initialContinuousCoefficient_product_integrable`
- `h3Audit_initialRelativeEnergy_exact_of_continuousIntegratedCoefficient`
- `h3Audit_initialScalarEnergy_zero_of_continuousIntegratedCoefficient`
- `H3AuditInitialCanonicalContinuousIntegratedCoefficientRelativeEnergyData`
- `h3Audit_initialContinuousIntegratedCoefficient_implies_timeIntegratedCoefficientData`
- `h3Audit_initialContinuousIntegratedCoefficient_implies_compactWeakComparisonData`
- `h3Audit_initialContinuousIntegratedCoefficient_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialContinuousIntegratedCoefficient`

## Unresolved mathematical obligations

This does not prove that the actual Navier–Stokes velocity supplies a
continuous initial-time coefficient, scalar energy integrability, an
old/selected relative-energy inequality or epsilon-vanishing residuals.
Strong-H³ terminal vorticity regularity is independently assumed in the
full-time theorem. The initial open-time PDE interface is not closed.
