import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Landau.Clock.Obstruction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Indexed.Energy.Sequence

/-!
# Quantifying the physical clock gap in the Landau majorant

The Riccati energy lower bound under hypothetical nonextension is
`4 ≤ K² (T-t)² E(t)`. The current Landau coefficient is at least one,
so its transport majorant `c_L(t) E(t)` has at least the same inverse
square physical rate. Cubing shows an explicit inverse-fourth-power
gap in the physical quantity `(T-t)² (c_L E)³`. This is a property of
the available upper majorant, not a lower estimate for actual
transport or dissipation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The current Landau coefficient is at least one at every time. -/
theorem one_le_canonicalLandauTransportCoefficient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    1 ≤ h3PathCanonicalLandauTransportCoefficient u t := by
  have hProduct :
      0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  unfold h3PathCanonicalLandauTransportCoefficient
  linarith

/-- The Riccati energy bound also applies to the current Landau
transport majorant at every strict preterminal time. -/
theorem four_le_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_LandauMajorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    4 ≤ h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (T - t) ^ 2 *
        (h3PathCanonicalLandauTransportCoefficient u t *
          velocityH3EnergyAt u t) := by
  have hEnergyOne : 1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t
  have hEnergyLeMajorant :
      velocityH3EnergyAt u t ≤
        h3PathCanonicalLandauTransportCoefficient u t *
          velocityH3EnergyAt u t := by
    simpa using mul_le_mul_of_nonneg_right
      (one_le_canonicalLandauTransportCoefficient u t)
      (by linarith : 0 ≤ velocityH3EnergyAt u t)
  have hPrefactor :
      0 ≤ h3PathSqrtEnergyRiccatiCoefficient ^ 2 * (T - t) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact
    (four_le_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_energy_of_noH3PathExtension
      hH3 hNoExtension hClass ht).trans
      (mul_le_mul_of_nonneg_left hEnergyLeMajorant hPrefactor)

/-- Cubing the inverse-square Landau-majorant bound gives an explicit
inverse-fourth-power gap in its physical cubic clock. -/
theorem LandauMajorant_physicalCubic_inverseFourthGap_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    64 ≤ h3PathSqrtEnergyRiccatiCoefficient ^ 6 *
      (T - t) ^ 4 *
        ((T - t) ^ 2 *
          (h3PathCanonicalLandauTransportCoefficient u t *
            velocityH3EnergyAt u t) ^ 3) := by
  have hRate :=
    four_le_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_LandauMajorant
      hH3 hNoExtension hClass ht
  have hCube := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 4) hRate 3
  calc
    (64 : ℝ) = (4 : ℝ) ^ 3 := by norm_num
    _ ≤ (h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (T - t) ^ 2 *
            (h3PathCanonicalLandauTransportCoefficient u t *
              velocityH3EnergyAt u t)) ^ 3 := hCube
    _ = h3PathSqrtEnergyRiccatiCoefficient ^ 6 *
          (T - t) ^ 4 *
            ((T - t) ^ 2 *
              (h3PathCanonicalLandauTransportCoefficient u t *
                velocityH3EnergyAt u t) ^ 3) := by ring

end

end Euclidean
end Bridge
end PrimeTensor
