# Initial relative-energy uniqueness from integrated residual densities

Base: `497b3cdf` — derive initial uniqueness from variable relative energy residuals.

## New sufficient criterion

Rather than supplying a time-indexed scalar budget `ρ n t ≤ δ n`, the PDE side
supplies a real residual-density family `R n s` that is absolutely integrable
on `[0,b]` and satisfies

    ∫₀ᵇ |Rₙ(s)| ds → 0  as n → ∞.

The approximate inequality is

    ‖D(t)‖² ≤ κₙ ∫₀ᵗ ‖D(s)‖² ds + ∫₀ᵗ |Rₙ(s)| ds,

with all `κₙ` bounded above by one `K`. Monotonicity of the integral of a
nonnegative function gives the residual budget required by the existing
variable-residual theorem. No pointwise convergence or uniform sup-norm bound
on `Rₙ` is needed.

## Formal declarations

- `h3Audit_initialResidualPrimitive_le_totalAbsMass`
- `h3Audit_initialRelativeEnergy_exact_of_integratedResidual`
- `H3AuditInitialCanonicalIntegratedResidualRelativeEnergyData`
- `h3Audit_initialIntegratedResidual_implies_variableResidualData`
- `h3Audit_initialIntegratedResidual_implies_compactWeakComparisonData`
- `h3Audit_initialIntegratedResidual_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialIntegratedResidual`

## Explicit remaining obligations

The analytic PDE estimates yielding the approximate inequality and the L¹
vanishing of `Rₙ` are not derived here. Neither is initial scalar-relative-
energy continuity of the artificially anchored old/selected difference.
The actual initial H³ Fourier-compatible datum and the terminal physical
strong-H³ vorticity endpoint also remain distinct assumptions.

This is a conditional interface improvement, not a Navier–Stokes global
regularity proof. No new axioms, `sorry`, or `admit` are used in the proposed
source. Lean/mathlib compilation is not performed in the patch environment.
