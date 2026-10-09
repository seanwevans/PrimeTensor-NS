import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourcePhysicalDichotomy

/-!
# The signed gradient obstruction has a strict physical spectral corridor

The fixed directed-source physical dichotomy retains two logically distinct
nonextension mechanisms.  The gradient-excess source has the form

  24 C1 sqrt(E) E3 - D.

Whenever this source is positive, top dissipation D3 <= D and the exact
intrinsic identity Lambda3^2 = D3/E3 imply the strict pointwise inequality

  Lambda3^2 < 24 C1 sqrt(E).

The signed ordered-monomial alternative is unchanged, including its fixed
velocity-component pair and all three critical physical clocks.

As a conditional consequence, if the reverse spectral barrier and a uniform
lower bound on every physical ordered monomial hold on one strict terminal
tail, the path extends.  Neither physical bound is asserted automatically.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Positivity of the actual gradient-excess channel forces an upper bound on
intrinsic top-order frequency. This uses top dissipative coercivity, not an
assumed negative sign of a velocity-component monomial. -/
private theorem h3PathCanonical_gradientExcess_pos_forces_spectralCorridor
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (hPositive :
      0 < 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
          velocityH3Energy3At u t - velocityH3DissipationAt u t) :
    h3TopCharacteristicFrequencyAt u t ^ 2 <
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hE3 : 0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg u t
  have hE3Pos : 0 < velocityH3Energy3At u t := by
    by_contra hNot
    have hZero : velocityH3Energy3At u t = 0 :=
      le_antisymm (le_of_not_gt hNot) hE3
    rw [hZero, mul_zero] at hPositive
    linarith only [hPositive, hD]
  have hD3Le : velocityH3Dissipation3At u t ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt u t
  have hUpper :
      velocityH3Dissipation3At u t <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) *
            velocityH3Energy3At u t := by
    linarith only [hPositive, hD3Le]
  have hRatio :
      velocityH3Dissipation3At u t / velocityH3Energy3At u t <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) :=
    (div_lt_iff₀ hE3Pos).2 hUpper
  rw [h3TopCharacteristicFrequencyAt_sq]
  exact hRatio

/-- On the existing fixed directed-source sequence, either the gradient
source occupies a strict intrinsic-frequency corridor eventually, or one
fixed ordered physical monomial has a negatively diverging H3-energy ratio.
The common terminal sequence and three clocks are retained exactly. -/
theorem h3PathCanonical_fixedDirectedSource_spectralCorridor_or_signedMonomial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo
        (T - (1 : ℝ) / ((n : ℝ) + 1)) T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ =>
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) atTop atTop ∧
      Tendsto (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
        atTop atTop ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (τ n)) ∧
      ((i = 0 ∧
          ∀ᶠ n : ℕ in atTop,
            h3TopCharacteristicFrequencyAt u (τ n) ^ 2 <
              24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                Real.sqrt (velocityH3EnergyAt u (τ n)))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            Tendsto
              (fun n : ℕ =>
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n)) atTop atTop)) := by
  obtain ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_physicalDichotomy_criticalClocks
      hH3 hNoExtension hClass hb
  refine ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks, ?_⟩
  rcases hAlternative with ⟨hZero, _hGradientT⟩ | ⟨hNe, j, r, hSignedT⟩
  · left
    refine ⟨hZero, ?_⟩
    have hLarge : ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) ≤
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n)) :=
      (tendsto_atTop.1 hSourceT) 1
    filter_upwards [hLarge] with n hn
    have hE : 0 < velocityH3EnergyAt u (τ n) :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u (τ n))
    have hDen : 0 < 9 * velocityH3EnergyAt u (τ n) := by
      positivity
    have hNum :
        9 * velocityH3EnergyAt u (τ n) ≤
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i := by
      simpa only [one_mul] using (le_div_iff₀ hDen).mp hn
    have hPositive : 0 < h3PathCanonicalJointDirectedTenSourceAt u (τ n) i :=
      lt_of_lt_of_le hDen hNum
    have hGradientPositive :
        0 < 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n))) *
            velocityH3Energy3At u (τ n) -
              velocityH3DissipationAt u (τ n) := by
      simpa [hZero, h3PathCanonicalJointDirectedTenSourceAt] using hPositive
    exact h3PathCanonical_gradientExcess_pos_forces_spectralCorridor
      u (τ n) hGradientPositive
  · right
    exact ⟨hNe, j, r, hSignedT⟩

/-- A late-time spectral lower barrier removes the gradient-excess branch;
if every ordered physical first-monomial is also bounded below at full-H3
energy scale, the signed-source alternative rules out nonextension.
Both conditions are explicit and neither is derived from Navier--Stokes
in this theorem. -/
theorem h3PathCanonical_extension_of_spectralBarrier_and_signedMonomialCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hBarrier : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) ≤
        h3TopCharacteristicFrequencyAt u t ^ 2)
    (hSigned : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∀ j r : PrimeTensor.Axis Depth.three,
        -(2 * h3PathCanonicalFirstMonomialComponentAt u t j r) ≤
          K * velocityH3EnergyAt u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨i, τ, hNear, hτT, _hSourceT, _hFreqT, _hClocks,
      hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_spectralCorridor_or_signedMonomial
      hH3 hNoExtension hClass hb
  have hLate : ∀ᶠ n : ℕ in atTop, d < τ n :=
    (tendsto_order.1 hτT).1 d hd.2
  rcases hAlternative with ⟨_hZero, hCorridor⟩ | ⟨_hNe, j, r, hDiverge⟩
  · obtain ⟨n, hnLate, hnCorridor⟩ := (hLate.and hCorridor).exists
    have hLower := hBarrier (τ n) ⟨hnLate, (hNear n).2⟩
    exact (not_lt_of_ge hLower) hnCorridor
  · have hBound : ∀ᶠ n : ℕ in atTop,
        -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
          velocityH3EnergyAt u (τ n) ≤ K := by
      filter_upwards [hLate] with n hnLate
      have hE : 0 < velocityH3EnergyAt u (τ n) :=
        lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u (τ n))
      exact (div_le_iff₀ hE).2
        (hSigned (τ n) ⟨hnLate, (hNear n).2⟩ j r)
    have hLarge : ∀ᶠ n : ℕ in atTop,
        K + 1 ≤
          -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
            velocityH3EnergyAt u (τ n) :=
      (tendsto_atTop.1 hDiverge) (K + 1)
    obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
    linarith only [hnBound, hnLarge]

end
end Euclidean
end Bridge
end PrimeTensor
