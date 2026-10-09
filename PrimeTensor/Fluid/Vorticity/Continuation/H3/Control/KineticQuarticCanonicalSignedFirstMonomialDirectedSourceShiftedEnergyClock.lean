import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourcePhysicalEnergyClock

/-!
# Fixed directed H³ gradient source forces every shifted physical energy clock

The exact signed gradient-source obstruction is more quantitative than its
strict spectral corridor. If its H³-normalized source exceeds a prescribed
`R >= 0`, the established physical spectral-gap lemma proves

  Lambda3(t)^2 < 24 C1 sqrt(E(t)) - 9 R.

The independently established frequency clock at the same physical time
then forces

  1 < 3 K^2 (E0(b)+1) (T-t)^2 (24 C1 sqrt(E(t)) - 9 R)^3.

On a fixed gradient-source terminal sequence the normalized source tends
to `+infinity`, so this strict shifted clock holds eventually for *each*
fixed nonnegative `R`. This is a quantifier over constant thresholds, not
a claim that one index-dependent threshold works at every selected time.

The alternative is a single fixed ordered signed velocity monomial whose
negative normalized contribution tends to `+infinity`. Both branches retain
the same times, fixed source, and the three physical critical clocks.
Nothing proves the shifted clock's reverse inequality or bounds the signed
monomials unconditionally.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Strict critical physical-time energy clock after spending `9 R` of the
physical gradient/frequency spectral budget. -/
def h3PathCanonicalGradientShiftedEnergyClockAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t R : ℝ) : Prop :=
  1 <
    3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1) * (T - t) ^ 2 *
      (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) - 9 * R) ^ 3

/-- An arbitrary fixed positive gradient-source rate forces a *shifted*
critical physical energy clock through the actual top-order frequency. -/
theorem h3PathCanonical_gradientSource_rate_forces_shiftedEnergyClock
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t R : ℝ)
    (ht : t < T)
    (hR : 0 ≤ R)
    (hClock :
      1 ≤ 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3Energy0At u b + 1) * (T - t) ^ 2 *
          h3TopCharacteristicFrequencyAt u t ^ 6)
    (hLarge :
      R <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
          velocityH3Energy3At u t - velocityH3DissipationAt u t) /
          (9 * velocityH3EnergyAt u t)) :
    h3PathCanonicalGradientShiftedEnergyClockAt u T b t R := by
  have hGap :=
    h3PathCanonical_gradientSource_rate_forces_spectralGap
      u t R hR hLarge
  have hShiftedCorridor :
      h3TopCharacteristicFrequencyAt u t ^ 2 <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) - 9 * R := by
    linarith only [hGap]
  have hE0 : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hRic : 0 < h3PathSqrtEnergyRiccatiCoefficient :=
    h3PathSqrtEnergyRiccatiCoefficient_pos
  have hDistance : 0 < T - t := sub_pos.mpr ht
  have hPref :
      0 < 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3Energy0At u b + 1) * (T - t) ^ 2 := by
    positivity
  have hFreqSq : 0 ≤ h3TopCharacteristicFrequencyAt u t ^ 2 :=
    sq_nonneg _
  have hCube :
      (h3TopCharacteristicFrequencyAt u t ^ 2) ^ 3 <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) - 9 * R) ^ 3 :=
    pow_lt_pow_left₀ hShiftedCorridor hFreqSq (by norm_num)
  have hSix :
      h3TopCharacteristicFrequencyAt u t ^ 6 <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) - 9 * R) ^ 3 := by
    calc
      _ = (h3TopCharacteristicFrequencyAt u t ^ 2) ^ 3 := by ring
      _ < _ := hCube
  have hScaled := mul_lt_mul_of_pos_left hSix hPref
  change 1 <
    3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1) * (T - t) ^ 2 *
      (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) - 9 * R) ^ 3
  exact lt_of_le_of_lt hClock hScaled

/-- Hypothetical nonextension has one fixed signed source and actual terminal
times supporting every fixed nonnegative shifted physical gradient clock, or
one fixed ordered adverse velocity monomial. All three physical critical
clocks remain synchronized on exactly these times. -/
theorem h3PathCanonical_fixedDirectedSource_shiftedEnergyClock_or_signedMonomial
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
          ∀ R : ℝ, 0 ≤ R →
            (∀ᶠ n : ℕ in atTop,
              h3PathCanonicalGradientShiftedEnergyClockAt
                u T b (τ n) R)) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            Tendsto
              (fun n : ℕ =>
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n)) atTop atTop)) := by
  obtain ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks,
      hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_physicalDichotomy_criticalClocks
      hH3 hNoExtension hClass hb
  refine ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks, ?_⟩
  rcases hAlternative with ⟨hi, hGradientT⟩ | ⟨hi, j, r, hSignedT⟩
  · left
    refine ⟨hi, ?_⟩
    intro R hR
    have hLarge : ∀ᶠ n : ℕ in atTop,
        R + 1 ≤
          (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n))) *
            velocityH3Energy3At u (τ n) - velocityH3DissipationAt u (τ n)) /
            (9 * velocityH3EnergyAt u (τ n)) :=
      (tendsto_atTop.1 hGradientT) (R + 1)
    filter_upwards [hClocks, hLarge] with n hClockN hLargeN
    have hRStrict :
        R <
          (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n))) *
            velocityH3Energy3At u (τ n) - velocityH3DissipationAt u (τ n)) /
            (9 * velocityH3EnergyAt u (τ n)) := by
      linarith only [hLargeN]
    exact h3PathCanonical_gradientSource_rate_forces_shiftedEnergyClock
      u T b (τ n) R (hNear n).2 hR hClockN.1 hRStrict
  · right
    exact ⟨hi, j, r, hSignedT⟩

/-- A finite tail ceiling on *one* shifted physical gradient clock excludes
the gradient alternative. Together with uniform boundedness of the nine
ordered signed physical monomials it forces smooth continuation. Both
physical hypotheses remain explicit. -/
theorem h3PathCanonical_extension_of_shiftedEnergyClock_and_signedCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R)
    (hClockCeiling : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ¬ h3PathCanonicalGradientShiftedEnergyClockAt u T b t R)
    (hSignedCeiling : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∀ j r : PrimeTensor.Axis Depth.three,
        -(2 * h3PathCanonicalFirstMonomialComponentAt u t j r) /
          velocityH3EnergyAt u t ≤ K) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨i, τ, hNear, hτT, _hSourceT, _hFreqT, _hClocks,
      hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_shiftedEnergyClock_or_signedMonomial
      hH3 hNoExtension hClass hb
  have hLate : ∀ᶠ n : ℕ in atTop, d < τ n :=
    (tendsto_order.1 hτT).1 d hd.2
  rcases hAlternative with ⟨_hi, hShifted⟩ | ⟨_hi, j, r, hSignedT⟩
  · have hRate := hShifted R hR
    obtain ⟨n, hnLate, hnRate⟩ := (hLate.and hRate).exists
    exact (hClockCeiling (τ n) ⟨hnLate, (hNear n).2⟩) hnRate
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
