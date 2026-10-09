import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopSpectralCorridor

/-!
# Signed top-order spectral corridor meets the fourth Fourier moment

On any physically adverse third-order transport witness, the preceding file
establishes a positive top-order energy `E₃` and the strict Fourier corridor

    D₃ + M E < K E₃,     K = 4398 C₁ sqrt(E),    M >= 0.

The existing physical Fourier interpolation bound `E₃^4 <= E₀ D₃^3`
then forces `E₃ < E₀ K^3`, with no new analytic hypotheses. Since the
physical kinetic energy is antitone, `E₀(t)` may be replaced by a fixed
anchor `E₀(b)` for later times.

This is an additional *necessary* inequality on hypothetical nonextension
witnesses, not a contradiction: K^3 grows like E^(3/2), and the resulting
energy bound need not constrain E₃ <= E at high energy. Conversely, if the
opposite top-energy inequality holds at every time on a terminal tail,
nonextension is impossible. This is only a conditional continuation result.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- A positive fourth moment and a strict upper third-to-fourth frequency
corridor force the third moment below the kinetic mass times `K³`.
This lemma is purely real algebra, including the zero-mass corner case. -/
theorem h3PathCanonical_fourthMoment_strictCorridor_topEnergy_lt
    {m x d K : ℝ}
    (hm : 0 ≤ m)
    (hx : 0 < x)
    (hd : 0 ≤ d)
    (hMoment : x ^ 4 ≤ m * d ^ 3)
    (hCorridor : d < K * x) :
    x < m * K ^ 3 := by
  have hmPos : 0 < m := by
    by_contra hmNot
    have hmZero : m = 0 := le_antisymm (le_of_not_gt hmNot) hm
    rw [hmZero] at hMoment
    nlinarith only [hMoment, pow_pos hx 4]
  have hKx : 0 < K * x := lt_of_le_of_lt hd hCorridor
  have hDSquare : d * d ≤ (K * x) * (K * x) :=
    mul_self_le_mul_self hd hCorridor.le
  have hDCube : d ^ 3 < (K * x) ^ 3 := by
    calc
      d ^ 3 = (d * d) * d := by ring
      _ ≤ ((K * x) * (K * x)) * d :=
        mul_le_mul_of_nonneg_right hDSquare hd
      _ < ((K * x) * (K * x)) * (K * x) :=
        mul_lt_mul_of_pos_left hCorridor (mul_pos hKx hKx)
      _ = (K * x) ^ 3 := by ring
  have hUpper : x ^ 4 < m * (K * x) ^ 3 :=
    lt_of_le_of_lt hMoment (mul_lt_mul_of_pos_left hDCube hmPos)
  have hFactor : x ^ 3 * x < x ^ 3 * (m * K ^ 3) := by
    calc
      x ^ 3 * x = x ^ 4 := by ring
      _ < m * (K * x) ^ 3 := hUpper
      _ = x ^ 3 * (m * K ^ 3) := by ring
  by_contra hNot
  have hGe : m * K ^ 3 ≤ x := le_of_not_gt hNot
  have hContract := mul_le_mul_of_nonneg_left hGe (pow_nonneg hx.le 3)
  exact (not_le_of_gt hFactor) hContract

/-- In fact the fourth-moment constraint and a strict corridor already
imply a strict bound on top energy using the *current* kinetic mass. -/
theorem h3PathCanonical_signedTopCorridor_energy_lt_kineticGradientCube
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    velocityH3Energy3At u t <
      velocityH3Energy0At u t *
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 3 := by
  have hE3Pos := h3PathCanonical_topEnergy_pos_of_signedTransportDominance
    hH3 hClass ht hM hAdverse
  have hMoment :=
    velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
      hH3 hClass ht
  have hCorridor :=
    h3PathCanonical_topDissipation_add_growth_lt_LandauTopCeiling
      hH3 hClass ht hAdverse
  have hD3 : 0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg u t
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hGrowth : 0 ≤ M * velocityH3EnergyAt u t :=
    mul_nonneg hM hE
  have hFrequency : velocityH3Dissipation3At u t <
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t := by
    linarith only [hCorridor, hGrowth]
  exact h3PathCanonical_fourthMoment_strictCorridor_topEnergy_lt
    (velocityH3Energy0At_nonneg u t) hE3Pos hD3 hMoment hFrequency

/-- Kinetic monotonicity anchors the fourth-moment spectral restriction
uniformly at an earlier physical time b. -/
theorem h3PathCanonical_signedTopCorridor_energy_lt_anchoredKineticGradientCube
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    velocityH3Energy3At u t <
      velocityH3Energy0At u b *
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 3 := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hPhysical :=
    h3PathCanonical_signedTopCorridor_energy_lt_kineticGradientCube
      hH3 hClass htClass hM hAdverse
  have hAnti : AntitoneOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3 hClass
  have hKinetic : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    hAnti hb htClass (le_of_lt ht.1)
  have hK : 0 ≤
      4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) :=
    mul_nonneg (by norm_num)
      (mul_nonneg
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg _))
  exact lt_of_lt_of_le hPhysical
    (mul_le_mul_of_nonneg_right hKinetic (pow_nonneg hK 3))

/-- The growth allowance in the signed Fourier corridor cannot exceed the
canonical gradient scale, because the top-energy block is part of total E. -/
theorem h3PathCanonical_signedTopCorridor_growthRate_lt_gradientScale
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    M < 4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) := by
  have hCorridor :=
    h3PathCanonical_topDissipation_add_growth_lt_LandauTopCeiling
      hH3 hClass ht hAdverse
  have hD3 : 0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg u t
  have hE0 : 0 ≤ velocityH3Energy0At u t :=
    velocityH3Energy0At_nonneg u t
  have hE1 : 0 ≤ velocityH3Energy1At u t :=
    velocityH3Energy1At_nonneg u t
  have hE2 : 0 ≤ velocityH3Energy2At u t :=
    velocityH3Energy2At_nonneg u t
  have hE3Le : velocityH3Energy3At u t ≤ velocityH3EnergyAt u t := by
    unfold velocityH3EnergyAt
    linarith only [hE0, hE1, hE2]
  have hK : 0 ≤
      4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) :=
    mul_nonneg (by norm_num)
      (mul_nonneg
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg _))
  have hScaled := mul_le_mul_of_nonneg_left hE3Le hK
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hProduct : M * velocityH3EnergyAt u t <
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3EnergyAt u t := by
    linarith only [hCorridor, hD3, hScaled]
  by_contra hNot
  have hGe :
      4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) ≤ M := le_of_not_gt hNot
  have hScaledContradiction := mul_le_mul_of_nonneg_right hGe hEPos.le
  exact (not_le_of_gt hProduct) hScaledContradiction

/-- Nonextension forces an actual selected time in *both* the strict
Fourier-frequency corridor and the anchored fourth-moment energy corridor,
with arbitrarily large prescribed logarithmic-growth allowance. -/
theorem h3PathCanonical_fourthMomentCorridor_on_every_strict_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      0 < velocityH3Energy3At u t ∧
      velocityH3Dissipation3At u t + M * velocityH3EnergyAt u t <
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t ∧
      velocityH3Energy3At u t <
        velocityH3Energy0At u b *
          (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t))) ^ 3 := by
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have htAnchor : t ∈ Set.Ioo b T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  exact ⟨t, ht,
    h3PathCanonical_topEnergy_pos_of_signedTransportDominance
      hH3 hClass htClass hM hAdverse,
    h3PathCanonical_topDissipation_add_growth_lt_LandauTopCeiling
      hH3 hClass htClass hAdverse,
    h3PathCanonical_signedTopCorridor_energy_lt_anchoredKineticGradientCube
      hH3 hClass hb htAnchor hM hAdverse⟩

/-- A conditional continuation criterion in terms of the current third
Fourier energy versus the earlier kinetic mass and the cube of the gradient
scale. It follows by excluding the *necessary* strict corridor above.
No estimate ensuring this condition for arbitrary solutions is asserted. -/
theorem h3PathCanonical_extension_of_eventual_topEnergy_above_kineticGradientCube
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hAbove : ∀ t : ℝ, t ∈ Set.Ioo d T →
      velocityH3Energy0At u b *
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 3 ≤
        velocityH3Energy3At u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd (by norm_num : (0 : ℝ) ≤ 0)
  have htAnchor : t ∈ Set.Ioo b T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hStrict :=
    h3PathCanonical_signedTopCorridor_energy_lt_anchoredKineticGradientCube
      hH3 hClass hb htAnchor (by norm_num : (0 : ℝ) ≤ 0) hAdverse
  exact (not_lt_of_ge (hAbove t ht)) hStrict

end Euclidean
end Bridge
end PrimeTensor
