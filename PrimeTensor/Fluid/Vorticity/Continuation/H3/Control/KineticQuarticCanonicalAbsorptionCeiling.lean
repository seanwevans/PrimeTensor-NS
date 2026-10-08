import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalMeasurability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Absorption.Landau.Harmonic.Rate

/-!
# Canonical square-root gradient confines the exact absorbed regime

A transport coefficient bounded below by K * sqrt(E), with K > 0, makes
activation of the quartic-absorbed branch satisfy 81 * M * K^2 * B < 8,
where M is the kinetic-energy mass at the anchor. Consequently the selected
absorbed coefficient obeys the uniform weighted bound 81 * M * K^2 * A <= 8.
For M > 0 this is an ordinary upper bound on the selected coefficient.
These pointwise estimates do not themselves prove temporal integrability.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- An active quartic absorption branch with a square-root-energy lower
bound on B forces a reciprocal bound on the product M * B. -/
theorem exact_kinetic_quartic_activation_weighted_coefficient_ceiling
    {B M E K : ℝ}
    (hB : 0 < B) (hM : 0 ≤ M) (hE : 0 < E) (hK : 0 < K)
    (hSqrt : K * Real.sqrt E ≤ B)
    (hHigh : 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M < E) :
    81 * M * K ^ 2 * B < 8 := by
  have hSqrtNonneg : 0 ≤ K * Real.sqrt E :=
    mul_nonneg (le_of_lt hK) (Real.sqrt_nonneg E)
  have hSquare : 0 ≤ (B - K * Real.sqrt E) * (B + K * Real.sqrt E) :=
    mul_nonneg (sub_nonneg.mpr hSqrt)
      (add_nonneg (le_of_lt hB) hSqrtNonneg)
  have hScale : K ^ 2 * E ≤ B ^ 2 := by
    rw [← Real.sq_sqrt (le_of_lt hE)]
    nlinarith only [hSquare]
  have hRest : 0 ≤ 1 + 3 * M := by
    linarith only [hM]
  have hThreshold : (81 / 8 : ℝ) * M * B ^ 3 < E := by
    nlinarith only [hHigh, hRest]
  have hScaled := mul_lt_mul_of_pos_right hThreshold (pow_pos hK 2)
  by_contra hNot
  have hLarge : 8 ≤ 81 * M * K ^ 2 * B := le_of_not_gt hNot
  have hMultiply := mul_le_mul_of_nonneg_right hLarge (sq_nonneg B)
  nlinarith only [hScaled, hScale, hMultiply]

/-- With an energy-dependent lower bound on B, the selected absorbed branch
has a uniform weighted ceiling, even across arbitrary threshold crossings. -/
theorem exact_kinetic_quartic_selected_absorbed_weighted_ceiling
    {B M E K : ℝ}
    (hB : 0 < B) (hM : 0 ≤ M) (hE : 0 < E) (hK : 0 < K)
    (hSqrt : K * Real.sqrt E ≤ B) :
    81 * M * K ^ 2 *
      (if E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M
       then 0 else (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M) / E)
      ≤ 8 := by
  by_cases hLow : E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M
  · simp only [if_pos hLow, mul_zero]
    norm_num
  · have hHigh : 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M < E :=
      lt_of_not_ge hLow
    have hCeiling := exact_kinetic_quartic_activation_weighted_coefficient_ceiling
      hB hM hE hK hSqrt hHigh
    have hSmaller :
        (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M) / E < B :=
      (h3_exact_quartic_coefficient_lt_direct_iff hB hE).2 hHigh
    have hFactor : 0 ≤ 81 * M * K ^ 2 := by positivity
    have hScaled := mul_le_mul_of_nonneg_left (le_of_lt hSmaller) hFactor
    simp only [if_neg hLow]
    linarith only [hScaled, hCeiling]

/-- Explicit canonical coefficient for the already-closed H3 square-root
velocity-gradient envelope. -/
noncomputable def h3PathCanonicalKineticTransportCoefficient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : ℝ → ℝ :=
  fun t => 4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u t|)

/-- The canonical coefficient is strictly positive at every time. -/
theorem h3PathCanonicalKineticTransportCoefficient_pos
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    0 < h3PathCanonicalKineticTransportCoefficient u t := by
  unfold h3PathCanonicalKineticTransportCoefficient
  nlinarith [abs_nonneg (h3PathCanonicalSqrtEnergyGradientEnvelope u t)]

/-- The canonical transport coefficient dominates a positive multiple of
the square root of the normalized H3 energy. -/
theorem h3PathCanonicalKineticTransportCoefficient_sqrt_lower
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
        Real.sqrt (velocityH3EnergyAt u t) ≤
      h3PathCanonicalKineticTransportCoefficient u t := by
  have hC : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    le_of_lt h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
  have hProd : 0 ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg hC (Real.sqrt_nonneg _)
  unfold h3PathCanonicalKineticTransportCoefficient
    h3PathCanonicalSqrtEnergyGradientEnvelope
  rw [abs_of_nonneg hProd]
  nlinarith

/-- Every canonical selected absorbed share satisfies the same weighted
pointwise bound, including times where the selected share vanishes. -/
theorem h3PathCanonicalSelectedAbsorbedCoefficient_weighted_ceiling
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ) :
    81 * velocityH3Energy0At u b *
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t ≤ 8 := by
  have hB := h3PathCanonicalKineticTransportCoefficient_pos u t
  have hM := velocityH3Energy0At_nonneg u b
  have hE : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hCPos : 0 < h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
  have hK : 0 < 4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient := by
    positivity
  have hLower := h3PathCanonicalKineticTransportCoefficient_sqrt_lower u t
  simpa only [h3ExactAdaptiveSelectedAbsorbedCoefficient] using
    (exact_kinetic_quartic_selected_absorbed_weighted_ceiling
      (B := h3PathCanonicalKineticTransportCoefficient u t)
      (M := velocityH3Energy0At u b)
      (E := velocityH3EnergyAt u t)
      (K := 4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient)
      hB hM hE hK hLower)

/-- A positive kinetic anchor turns the weighted pointwise ceiling into an
ordinary finite bound for its canonical selected absorbed coefficient. -/
theorem h3PathCanonicalSelectedAbsorbedCoefficient_le_of_positive_kinetic_mass
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ)
    (hMass : 0 < velocityH3Energy0At u b) :
    h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t ≤
      8 / (81 * velocityH3Energy0At u b *
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2) := by
  have hC : 0 < h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
  have hDen : 0 < 81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 := by
    positivity
  apply (le_div_iff₀ hDen).2
  have hBound := h3PathCanonicalSelectedAbsorbedCoefficient_weighted_ceiling u b t
  nlinarith only [hBound]

end Euclidean
end Bridge
end PrimeTensor
