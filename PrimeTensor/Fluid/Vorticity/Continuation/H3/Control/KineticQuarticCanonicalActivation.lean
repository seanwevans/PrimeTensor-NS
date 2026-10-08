import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalAbsorbedIntegrability

/-!
# Canonical kinetic activation is confined to bounded H3 energy

At a fixed kinetic anchor M, the exact absorbed branch is activated only if

  E > 1 + (3 + (81/8) B^3) M.

For B at least K * sqrt(E), with K positive, the preceding activation-ceiling
result forces 81 M K^2 B < 8 and thus 81 M K^3 sqrt(E) < 8.
Conversely, crossing either bound forces the *direct* branch pointwise.

In particular, with the canonical sqrt-H3-energy gradient envelope, a
hypothetical high-energy excursion cannot select the absorbed branch. This
is a conditional pointwise regime classification, not a bound on the time
spent in the direct regime or a proof of continuation/nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- A sufficiently large coefficient rules out exact quartic activation. -/
theorem exact_kinetic_quartic_direct_of_weighted_coefficient_large
    {B M E K : ℝ}
    (hB : 0 < B) (hM : 0 ≤ M) (hE : 0 < E) (hK : 0 < K)
    (hSqrt : K * Real.sqrt E ≤ B)
    (hLarge : 8 ≤ 81 * M * K ^ 2 * B) :
    E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M := by
  by_contra hNot
  have hHigh : 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M < E :=
    lt_of_not_ge hNot
  have hCeiling := exact_kinetic_quartic_activation_weighted_coefficient_ceiling
    hB hM hE hK hSqrt hHigh
  exact (not_lt_of_ge hLarge) hCeiling

/-- Above the weighted coefficient threshold, the selected scalar direct
share is the whole transport coefficient. -/
theorem exact_kinetic_quartic_selected_direct_eq_of_weighted_coefficient_large
    {B M E K : ℝ}
    (hB : 0 < B) (hM : 0 ≤ M) (hE : 0 < E) (hK : 0 < K)
    (hSqrt : K * Real.sqrt E ≤ B)
    (hLarge : 8 ≤ 81 * M * K ^ 2 * B) :
    (if E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M then B else 0) = B := by
  have hDirect := exact_kinetic_quartic_direct_of_weighted_coefficient_large
    hB hM hE hK hSqrt hLarge
  simp only [if_pos hDirect]

/-- An activated absorbed regime confines the square root of the energy,
with no division by the kinetic mass. -/
theorem exact_kinetic_quartic_active_sqrt_energy_ceiling
    {B M E K : ℝ}
    (hB : 0 < B) (hM : 0 ≤ M) (hE : 0 < E) (hK : 0 < K)
    (hSqrt : K * Real.sqrt E ≤ B)
    (hHigh : 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M < E) :
    81 * M * K ^ 3 * Real.sqrt E < 8 := by
  have hCeiling := exact_kinetic_quartic_activation_weighted_coefficient_ceiling
    hB hM hE hK hSqrt hHigh
  have hFactor : 0 ≤ 81 * M * K ^ 2 := by positivity
  calc
    81 * M * K ^ 3 * Real.sqrt E =
        (81 * M * K ^ 2) * (K * Real.sqrt E) := by ring
    _ ≤ (81 * M * K ^ 2) * B :=
      mul_le_mul_of_nonneg_left hSqrt hFactor
    _ < 8 := hCeiling

/-- Canonical transport coefficient above the kinetic threshold forces direct
selection at the specified time and kinetic anchor. -/
theorem h3PathCanonical_direct_regime_of_weighted_transport_large
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ)
    (hLarge : 8 ≤ 81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
      h3PathCanonicalKineticTransportCoefficient u t) :
    velocityH3EnergyAt u t ≤
      1 + (3 + (81 / 8 : ℝ) *
        (h3PathCanonicalKineticTransportCoefficient u t) ^ 3) *
          velocityH3Energy0At u b := by
  have hK : 0 < 4422 *
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient := by
    have hC := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
    positivity
  exact exact_kinetic_quartic_direct_of_weighted_coefficient_large
    (h3PathCanonicalKineticTransportCoefficient_pos u t)
    (velocityH3Energy0At_nonneg u b)
    (lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t))
    hK
    (h3PathCanonicalKineticTransportCoefficient_sqrt_lower u t)
    hLarge

/-- The selected direct share agrees with the entire canonical gradient
coefficient above the weighted transport threshold. -/
theorem h3PathCanonical_selected_direct_eq_transport_of_weighted_large
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ)
    (hLarge : 8 ≤ 81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
      h3PathCanonicalKineticTransportCoefficient u t) :
    h3ExactAdaptiveSelectedDirectCoefficient u
      (h3PathCanonicalKineticTransportCoefficient u) b t =
        h3PathCanonicalKineticTransportCoefficient u t := by
  have hDirect := h3PathCanonical_direct_regime_of_weighted_transport_large
    u b t hLarge
  unfold h3ExactAdaptiveSelectedDirectCoefficient
  simp only [if_pos hDirect]

/-- Above the weighted transport threshold, the selected absorbed share is
identically zero at the specified time. -/
theorem h3PathCanonical_selected_absorbed_eq_zero_of_weighted_large
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ)
    (hLarge : 8 ≤ 81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
      h3PathCanonicalKineticTransportCoefficient u t) :
    h3ExactAdaptiveSelectedAbsorbedCoefficient u
      (h3PathCanonicalKineticTransportCoefficient u) b t = 0 := by
  have hDirect := h3PathCanonical_direct_regime_of_weighted_transport_large
    u b t hLarge
  unfold h3ExactAdaptiveSelectedAbsorbedCoefficient
  simp only [if_pos hDirect]

/-- Large canonical H3 square-root energy forces direct selection, without
an a priori lower bound on the kinetic mass beyond nonnegativity. -/
theorem h3PathCanonical_direct_regime_of_sqrt_energy_large
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ)
    (hLarge : 8 ≤ 81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
      Real.sqrt (velocityH3EnergyAt u t)) :
    velocityH3EnergyAt u t ≤
      1 + (3 + (81 / 8 : ℝ) *
        (h3PathCanonicalKineticTransportCoefficient u t) ^ 3) *
          velocityH3Energy0At u b := by
  have hM : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hFactor : 0 ≤ 81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 := by
    positivity
  have hWeighted : 8 ≤ 81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
      h3PathCanonicalKineticTransportCoefficient u t := by
    calc
      8 ≤ 81 * velocityH3Energy0At u b *
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
          Real.sqrt (velocityH3EnergyAt u t) := hLarge
      _ = (81 * velocityH3Energy0At u b *
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2) *
          ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t)) := by ring
      _ ≤ (81 * velocityH3Energy0At u b *
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2) *
          h3PathCanonicalKineticTransportCoefficient u t :=
        mul_le_mul_of_nonneg_left
          (h3PathCanonicalKineticTransportCoefficient_sqrt_lower u t) hFactor
  exact h3PathCanonical_direct_regime_of_weighted_transport_large u b t hWeighted

/-- The canonical absorbed regime itself gives a fixed upper bound on sqrt H3
energy at a selected time. -/
theorem h3PathCanonical_absorption_active_sqrt_energy_ceiling
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ)
    (hHigh : 1 + (3 + (81 / 8 : ℝ) *
      (h3PathCanonicalKineticTransportCoefficient u t) ^ 3) *
        velocityH3Energy0At u b < velocityH3EnergyAt u t) :
    81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
        Real.sqrt (velocityH3EnergyAt u t) < 8 := by
  have hK : 0 < 4422 *
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient := by
    have hC := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
    positivity
  exact exact_kinetic_quartic_active_sqrt_energy_ceiling
    (h3PathCanonicalKineticTransportCoefficient_pos u t)
    (velocityH3Energy0At_nonneg u b)
    (lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t))
    hK
    (h3PathCanonicalKineticTransportCoefficient_sqrt_lower u t)
    hHigh

end Euclidean
end Bridge
end PrimeTensor
