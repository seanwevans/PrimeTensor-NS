import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceSpectralCorridor

/-!
# Quantitative physical spectral gap on the fixed directed H³ obstruction

The earlier strict corridor only used positivity of the gradient-excess
source.  Retaining its *normalized magnitude* gives the sharper pointwise
estimate

  R < (24 C₁ sqrt(E) E₃ - D)/(9 E),  0 <= R
      ==> 9 R < 24 C₁ sqrt(E) - Lambda₃².

Indeed E₃ <= E and D₃ <= D, while Lambda₃² = D₃/E₃.
The premise also forces E₃ > 0, so all divisions are legitimate.

Therefore under hypothetical nonextension the original fixed-source
sequence has either a *divergent positive physical frequency gap* or one
fixed ordered signed velocity monomial with a divergent normalized deficit.
All previously established physical critical clocks stay on that sequence.

A uniform upper bound on the spectral gap and the signed velocity deficits
on one terminal tail forces continuation.  Neither bound is automatic.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- A positive normalized gradient excess consumes an explicit amount
`9 * R` of the physical frequency gap, not merely its sign. -/
theorem h3PathCanonical_gradientSource_rate_forces_spectralGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ)
    (hR : 0 ≤ R)
    (hLarge :
      R <
        (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
          velocityH3Energy3At u t - velocityH3DissipationAt u t) /
          (9 * velocityH3EnergyAt u t)) :
    9 * R <
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) -
        h3TopCharacteristicFrequencyAt u t ^ 2 := by
  let E : ℝ := velocityH3EnergyAt u t
  let E₃ : ℝ := velocityH3Energy3At u t
  let D : ℝ := velocityH3DissipationAt u t
  let D₃ : ℝ := velocityH3Dissipation3At u t
  let H : ℝ := 24 *
    (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * Real.sqrt E)
  have hE : 0 < E :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hDen : 0 < 9 * E := by positivity
  have hE₃ : 0 ≤ E₃ := velocityH3Energy3At_nonneg u t
  have hE₃Le : E₃ ≤ E := velocityH3Energy3At_le_velocityH3EnergyAt u t
  have hD : 0 ≤ D := velocityH3DissipationAt_nonneg u t
  have hD₃Le : D₃ ≤ D := velocityH3Dissipation3At_le_dissipationAt u t
  have hRNonneg : 0 ≤ 9 * R := mul_nonneg (by norm_num) hR
  have hRE : 0 ≤ (9 * R) * E := mul_nonneg hRNonneg hE.le
  have hScaled : (9 * R) * E < H * E₃ - D := by
    calc
      (9 * R) * E = R * (9 * E) := by ring
      _ < H * E₃ - D := by
        exact (lt_div_iff₀ hDen).mp (by simpa only [E, E₃, D, H] using hLarge)
  have hE₃Pos : 0 < E₃ := by
    by_contra hNot
    have hZero : E₃ = 0 := le_antisymm (le_of_not_gt hNot) hE₃
    rw [hZero, mul_zero] at hScaled
    linarith only [hScaled, hRE, hD]
  have hRE₃Le : (9 * R) * E₃ ≤ (9 * R) * E :=
    mul_le_mul_of_nonneg_left hE₃Le hRNonneg
  have hBudget : D₃ < (H - 9 * R) * E₃ := by
    nlinarith only [hScaled, hRE₃Le, hD₃Le]
  have hRatio : D₃ / E₃ < H - 9 * R :=
    (div_lt_iff₀ hE₃Pos).2 hBudget
  rw [h3TopCharacteristicFrequencyAt_sq]
  dsimp only [D₃, E₃, H, E] at hRatio
  linarith only [hRatio]

/-- The same fixed signed-source sequence and the same three physical
critical clocks satisfy one of two genuinely quantitative PDE obstructions:
a divergent intrinsic-frequency gap or an adverse ordered monomial. -/
theorem h3PathCanonical_fixedDirectedSource_spectralGap_or_signedMonomial
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
          Tendsto
            (fun n : ℕ =>
              24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                Real.sqrt (velocityH3EnergyAt u (τ n))) -
                h3TopCharacteristicFrequencyAt u (τ n) ^ 2)
              atTop atTop) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            Tendsto
              (fun n : ℕ =>
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n)) atTop atTop)) := by
  obtain ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks,
      hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_spectralCorridor_or_signedMonomial
      hH3 hNoExtension hClass hb
  refine ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks, ?_⟩
  rcases hAlternative with ⟨hi, _hCorridor⟩ | ⟨hi, j, r, hSignedT⟩
  · left
    refine ⟨hi, ?_⟩
    refine tendsto_atTop.2 ?_
    intro M
    let R : ℝ := max M 0 + 1
    have hR : 0 ≤ R := by
      dsimp only [R]
      have hMax : 0 ≤ max M 0 := le_max_right M 0
      linarith only [hMax]
    have hMR : M ≤ 9 * R := by
      dsimp only [R]
      have hMmax : M ≤ max M 0 := le_max_left M 0
      have hMax : 0 ≤ max M 0 := le_max_right M 0
      linarith only [hMmax, hMax]
    have hLarge : ∀ᶠ n : ℕ in atTop,
        R + 1 ≤
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n)) :=
      (tendsto_atTop.1 hSourceT) (R + 1)
    filter_upwards [hLarge] with n hn
    have hNormalized :
        R <
          (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n))) *
            velocityH3Energy3At u (τ n) -
            velocityH3DissipationAt u (τ n)) /
            (9 * velocityH3EnergyAt u (τ n)) := by
      have hStrict : R <
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n)) := by
        linarith only [hn]
      simpa [hi, h3PathCanonicalJointDirectedTenSourceAt] using hStrict
    have hGap :=
      h3PathCanonical_gradientSource_rate_forces_spectralGap
        u (τ n) R hR hNormalized
    exact le_of_lt (lt_of_le_of_lt hMR hGap)
  · right
    exact ⟨hi, j, r, hSignedT⟩

/-- If both the actual spectral gap and all nine ordered signed monomial
ratios admit some common finite ceiling on one terminal tail, the H³ path
extends.  This weakens the preceding theorem's zero-gap spectral barrier;
the quantitative gap may remain positive but not unbounded. -/
theorem h3PathCanonical_extension_of_eventualSpectralGap_and_signedCeilings
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hGap : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) -
          h3TopCharacteristicFrequencyAt u t ^ 2 ≤ K)
    (hSigned : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∀ j r : PrimeTensor.Axis Depth.three,
        -(2 * h3PathCanonicalFirstMonomialComponentAt u t j r) /
          velocityH3EnergyAt u t ≤ K) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨i, τ, hNear, hτT, _hSourceT, _hFreqT, _hClocks,
      hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_spectralGap_or_signedMonomial
      hH3 hNoExtension hClass hb
  have hLate : ∀ᶠ n : ℕ in atTop, d < τ n :=
    (tendsto_order.1 hτT).1 d hd.2
  rcases hAlternative with ⟨_hi, hGapT⟩ | ⟨_hi, j, r, hSignedT⟩
  · have hBound : ∀ᶠ n : ℕ in atTop,
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u (τ n))) -
          h3TopCharacteristicFrequencyAt u (τ n) ^ 2 ≤ K := by
      filter_upwards [hLate] with n hn
      exact hGap (τ n) ⟨hn, (hNear n).2⟩
    have hLarge : ∀ᶠ n : ℕ in atTop,
        K + 1 ≤ 24 *
          (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n))) -
          h3TopCharacteristicFrequencyAt u (τ n) ^ 2 :=
      (tendsto_atTop.1 hGapT) (K + 1)
    obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
    linarith only [hnBound, hnLarge]
  · have hBound : ∀ᶠ n : ℕ in atTop,
        -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
          velocityH3EnergyAt u (τ n) ≤ K := by
      filter_upwards [hLate] with n hn
      exact hSigned (τ n) ⟨hn, (hNear n).2⟩ j r
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
