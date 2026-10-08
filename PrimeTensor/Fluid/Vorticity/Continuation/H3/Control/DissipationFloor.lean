import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Dissipative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Integrability

/-!
# Dissipation absorption with an integrable nonlinear deficit

Write E for canonical H³ energy, D for its dissipation, and C₁ for the
spectral derivative-evaluation coefficient. The existing PDE estimate gives

  E' + 2 D ≤ 4422 E + 4422 C₁ sqrt(E) E.

If the nonlinear part is absorbed up to c(t) E, the remaining growth is
E' ≤ (4422 + c(t)) E. Integrability of c on one energy-class tail therefore
suffices for continuation. In particular, D ≥ 2211 C₁ sqrt(E) E suffices.

These are conditional estimates. No dissipation floor or integrable deficit
is asserted for every admissible path. No sqrt(E) integrability is assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory
open scoped Topology

/-- Full dissipation absorbs the nonlinear Landau term up to a scalar deficit. -/
theorem deriv_velocityH3EnergyAt_le_of_nonlinearDissipationDeficit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDeficit :
      4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t ≤
        2 * velocityH3DissipationAt u t + c * velocityH3EnergyAt u t) :
    deriv (velocityH3EnergyAt u) t ≤ (4422 + c) * velocityH3EnergyAt u t := by
  have hGrowth := deriv_velocityH3EnergyAt_add_two_dissipation_le_sqrtEnergyGrowth
    hH3 hClass ht
  have hNonneg :
      0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  rw [abs_of_nonneg hNonneg] at hGrowth
  nlinarith [hDeficit]

/-- An integrable nonlinear dissipation deficit on one tail implies continuation. -/
theorem h3PathExtension_of_integrableNonlinearDissipationDeficitOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {c : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hc : IntegrableOn c (Set.Ioo a T))
    (hDeficit : ∀ t : ℝ, t ∈ Set.Ioo a T →
      4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t ≤
        2 * velocityH3DissipationAt u t + c t * velocityH3EnergyAt u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hConstInterval :
      IntervalIntegrable (fun _ : ℝ => (4422 : ℝ)) volume a T :=
    intervalIntegrable_const
  have hConst : IntegrableOn (fun _ : ℝ => (4422 : ℝ)) (Set.Ioo a T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (le_of_lt hClass.terminal_start.2)).1 hConstInterval
  have hMajorant : IntegrableOn (fun t : ℝ => 4422 + c t) (Set.Ioo a T) :=
    hConst.add hc
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClass hMajorant
  intro t ht
  exact deriv_velocityH3EnergyAt_le_of_nonlinearDissipationDeficit
    hH3 hClass ht (hDeficit t ht)

/-- The explicit zero-deficit threshold absorbs all nonlinear sqrt-energy growth. -/
theorem h3PathExtension_of_nonlinearDissipationFloorOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hFloor : ∀ t : ℝ, t ∈ Set.Ioo a T →
      2211 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t ≤
        velocityH3DissipationAt u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hZero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioo a T) := by
    exact integrable_zero ℝ ℝ (volume.restrict (Set.Ioo a T))
  apply h3PathExtension_of_integrableNonlinearDissipationDeficitOnTail
    hH3 hClass hZero
  intro t ht
  have hFloorAt := hFloor t ht
  have hDouble :
      4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t ≤
        2 * velocityH3DissipationAt u t := by
    nlinarith [hFloorAt]
  simpa only [zero_mul, add_zero] using hDouble

end Euclidean
end Bridge
end PrimeTensor
