import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceSpectralGap

/-!
# Fixed signed H³ gradient source forces a critical physical energy clock

The nonextension source classification gives a common actual time sequence,
a fixed signed index, and three quantitative physical clocks. In its gradient
branch, the strict frequency corridor

  Lambda₃(t)^2 < 24 C₁ sqrt(E(t))

combines with the established frequency clock

  1 <= 3 K² (E₀(b)+1) (T-t)^2 Lambda₃(t)^6

to force the strict physical lower-rate condition

  1 < 3 K² (E₀(b)+1) (24 C₁)^3 (T-t)^2 sqrt(E(t))^3.

The energy factor has the scaling of E(t)^(3/2), giving the familiar
inverse-4/3 power as a *necessary gradient-branch physical rate*.
The alternative of one fixed ordered adverse velocity monomial is retained.
Nothing here supplies either an independent upper energy clock or a sign
estimate for the physical ordered monomial.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Combine the signed gradient spectral corridor with the independently
proved top-frequency terminal clock at the same physical time. -/
theorem h3PathCanonical_gradientCorridor_forces_physicalEnergyClock
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t : ℝ)
    (ht : t < T)
    (hClock :
      1 ≤ 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3Energy0At u b + 1) * (T - t) ^ 2 *
          h3TopCharacteristicFrequencyAt u t ^ 6)
    (hCorridor :
      h3TopCharacteristicFrequencyAt u t ^ 2 <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) :
    1 <
      3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3Energy0At u b + 1) *
        (24 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
        (T - t) ^ 2 * Real.sqrt (velocityH3EnergyAt u t) ^ 3 := by
  have hE0 : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hRic : 0 < h3PathSqrtEnergyRiccatiCoefficient :=
    h3PathSqrtEnergyRiccatiCoefficient_pos
  have hDist : 0 < T - t := sub_pos.mpr ht
  have hPref :
      0 < 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3Energy0At u b + 1) * (T - t) ^ 2 := by
    positivity
  have hSq : 0 ≤ h3TopCharacteristicFrequencyAt u t ^ 2 :=
    sq_nonneg _
  have hCube :
      (h3TopCharacteristicFrequencyAt u t ^ 2) ^ 3 <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 3 :=
    pow_lt_pow_left₀ hCorridor hSq (by norm_num)
  have hSix :
      h3TopCharacteristicFrequencyAt u t ^ 6 <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 3 := by
    calc
      _ = (h3TopCharacteristicFrequencyAt u t ^ 2) ^ 3 := by ring
      _ < _ := hCube
  have hScaled := mul_lt_mul_of_pos_left hSix hPref
  calc
    1 ≤ 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1) * (T - t) ^ 2 *
          h3TopCharacteristicFrequencyAt u t ^ 6 := hClock
    _ < 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1) * (T - t) ^ 2 *
          (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t))) ^ 3 := hScaled
    _ = _ := by ring

/-- Under hypothetical nonextension, one fixed signed source and one actual
terminal sequence carry all critical clocks, and either the gradient branch
obeys a critical physical-time lower energy rate or an ordered velocity
monomial has an adverse normalized divergence on precisely those times. -/
theorem h3PathCanonical_fixedDirectedSource_physicalEnergyClock_or_signedMonomial
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
            1 < 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
              (velocityH3Energy0At u b + 1) *
              (24 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
              (T - τ n) ^ 2 *
                Real.sqrt (velocityH3EnergyAt u (τ n)) ^ 3) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            Tendsto
              (fun n : ℕ =>
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n)) atTop atTop)) := by
  obtain ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_spectralCorridor_or_signedMonomial
      hH3 hNoExtension hClass hb
  refine ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks, ?_⟩
  rcases hAlternative with ⟨hZero, hCorridor⟩ | ⟨hNe, j, r, hSignedT⟩
  · left
    refine ⟨hZero, ?_⟩
    filter_upwards [hClocks, hCorridor] with n hnClock hnCorridor
    exact h3PathCanonical_gradientCorridor_forces_physicalEnergyClock
      u T b (τ n) (hNear n).2 hnClock.1 hnCorridor
  · right
    exact ⟨hNe, j, r, hSignedT⟩

/-- An eventual upper bound on the critical physical energy clock, coupled
with a uniform upper bound on all ordered adverse velocity monomial ratios,
excludes both fixed-source nonextension alternatives.  Neither premise is
asserted to follow automatically from the Navier--Stokes equations. -/
theorem h3PathCanonical_extension_of_physicalEnergyClock_and_signedCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hClockCeiling : ∀ t : ℝ, t ∈ Set.Ioo d T →
      3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3Energy0At u b + 1) *
        (24 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
        (T - t) ^ 2 * Real.sqrt (velocityH3EnergyAt u t) ^ 3 ≤ 1)
    (hSignedCeiling : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∀ j r : PrimeTensor.Axis Depth.three,
        -(2 * h3PathCanonicalFirstMonomialComponentAt u t j r) /
          velocityH3EnergyAt u t ≤ K) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨i, τ, hNear, hτT, _hSourceT, _hFreqT, _hClocks,
      hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_physicalEnergyClock_or_signedMonomial
      hH3 hNoExtension hClass hb
  have hLate : ∀ᶠ n : ℕ in atTop, d < τ n :=
    (tendsto_order.1 hτT).1 d hd.2
  rcases hAlternative with ⟨_hZero, hGradientRate⟩ | ⟨_hNe, j, r, hSignedT⟩
  · obtain ⟨n, hnLate, hnRate⟩ := (hLate.and hGradientRate).exists
    have hUpper := hClockCeiling (τ n) ⟨hnLate, (hNear n).2⟩
    exact (not_lt_of_ge hUpper) hnRate
  · have hBound : ∀ᶠ n : ℕ in atTop,
        -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
          velocityH3EnergyAt u (τ n) ≤ K := by
      filter_upwards [hLate] with n hn
      exact hSignedCeiling (τ n) ⟨hn, (hNear n).2⟩ j r
    have hLarge : ∀ᶠ n : ℕ in atTop,
        K + 1 ≤
          -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
            velocityH3EnergyAt u (τ n) :=
      (tendsto_atTop.1 hSignedT) (K + 1)
    obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
    linarith only [hnBound, hnLarge]

end
end Euclidean
end Bridge
end PrimeTensor
