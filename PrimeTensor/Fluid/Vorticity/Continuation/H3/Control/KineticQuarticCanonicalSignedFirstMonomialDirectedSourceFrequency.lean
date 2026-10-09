import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceThirdEnergyRatio
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Characteristic.Frequency.Rate

/-!
# Signed directed H³ source forces an intrinsic top-dissipation frequency cascade

The fixed ten-source nonextension sequence from the preceding module has
  E₃(τ n) / sqrt(E(τ n)) → +∞.
Since E >= 1, the very same times satisfy E₃(τ n) → +∞.

The *previously proved* Fourier moment interpolation and kinetic antitonicity
supply, on every strict kinetic-anchored tail, the physical estimate
  E₃(t) <= (E₀(b) + 1) * Λ₃(t)^6,
where Λ₃(t) = sqrt(D₃(t)/E₃(t)).  Thus the SAME fixed-source sequence has
  Λ₃(τ n) → +∞  and  D₃(τ n)/E₃(τ n) → +∞.

The source sign and frequency are synchronized, not selected on different
sequences. No universal upper bound for the characteristic frequency is
claimed, and no unconditional continuation/nonextension is derived.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Given an actual fixed directed-source nonextension sequence, the Fourier
moment inequality forces the intrinsic top-order characteristic frequency to
diverge on exactly the same times. -/
theorem h3PathCanonical_fixedDirectedSource_intrinsicFrequency_sameSequence
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
      Tendsto
        (fun n : ℕ =>
          velocityH3Energy3At u (τ n) /
            Real.sqrt (velocityH3EnergyAt u (τ n))) atTop atTop ∧
      Tendsto (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          velocityH3Dissipation3At u (τ n) /
            velocityH3Energy3At u (τ n)) atTop atTop := by
  obtain ⟨i, τ, hNear, hτT, hSourceT, hRatioT⟩ :=
    h3PathCanonical_fixedDirectedSource_thirdEnergyOverRoot_diverges
      hH3 hNoExtension hClass hb
  have hThirdT :
      Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    have hLarge : ∀ᶠ n : ℕ in atTop,
        M ≤ velocityH3Energy3At u (τ n) /
          Real.sqrt (velocityH3EnergyAt u (τ n)) :=
      (tendsto_atTop.1 hRatioT) M
    filter_upwards [hLarge] with n hn
    have hE3 : 0 ≤ velocityH3Energy3At u (τ n) :=
      velocityH3Energy3At_nonneg u (τ n)
    have hOne : 1 ≤ velocityH3EnergyAt u (τ n) :=
      one_le_velocityH3EnergyAt u (τ n)
    have hRootOne : (1 : ℝ) ≤
        Real.sqrt (velocityH3EnergyAt u (τ n)) := by
      simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt hOne)
    have hRootPos : 0 < Real.sqrt (velocityH3EnergyAt u (τ n)) :=
      lt_of_lt_of_le zero_lt_one hRootOne
    have hProd : velocityH3Energy3At u (τ n) ≤
        velocityH3Energy3At u (τ n) *
          Real.sqrt (velocityH3EnergyAt u (τ n)) := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hRootOne hE3)
    have hRatioLe :
        velocityH3Energy3At u (τ n) /
            Real.sqrt (velocityH3EnergyAt u (τ n)) ≤
          velocityH3Energy3At u (τ n) :=
      (div_le_iff₀ hRootPos).2 hProd
    exact le_trans hn hRatioLe
  have hLate : ∀ᶠ n : ℕ in atTop, b < τ n :=
    (tendsto_order.1 hτT).1 b hb.2
  let K : ℝ := velocityH3Energy0At u b + 1
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hE0 := velocityH3Energy0At_nonneg u b
    linarith only [hE0]
  have hFrequencyT :
      Tendsto (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    let Q : ℝ := K * (max M 0) ^ 6 + 1
    have hMax : 0 ≤ max M 0 := le_max_right M 0
    have hQPos : 0 < Q := by
      dsimp only [Q]
      have hPower : 0 ≤ (max M 0) ^ 6 := pow_nonneg hMax 6
      have hProduct : 0 ≤ K * (max M 0) ^ 6 :=
        mul_nonneg hK hPower
      linarith only [hProduct]
    have hLarge : ∀ᶠ n : ℕ in atTop,
        Q ≤ velocityH3Energy3At u (τ n) :=
      (tendsto_atTop.1 hThirdT) Q
    filter_upwards [hLate, hLarge] with n hn hThirdLarge
    have ht : τ n ∈ Set.Ioo b T := ⟨hn, (hNear n).2⟩
    have hE3Pos : 0 < velocityH3Energy3At u (τ n) :=
      lt_of_lt_of_le hQPos hThirdLarge
    have hBound :=
      velocityH3Energy3At_le_energy0Anchor_add_one_mul_characteristicFrequency_pow_six
        hH3 hClass hb ht hE3Pos
    by_contra hNot
    have hFreqBelow : h3TopCharacteristicFrequencyAt u (τ n) < M :=
      lt_of_not_ge hNot
    have hFreqLe : h3TopCharacteristicFrequencyAt u (τ n) ≤ max M 0 :=
      le_trans (le_of_lt hFreqBelow) (le_max_left M 0)
    have hFreqNonneg : 0 ≤ h3TopCharacteristicFrequencyAt u (τ n) :=
      h3TopCharacteristicFrequencyAt_nonneg u (τ n)
    have hPow : (h3TopCharacteristicFrequencyAt u (τ n)) ^ 6 ≤
        (max M 0) ^ 6 := by
      gcongr <;> assumption
    have hScaled :
        K * (h3TopCharacteristicFrequencyAt u (τ n)) ^ 6 ≤
          K * (max M 0) ^ 6 :=
      mul_le_mul_of_nonneg_left hPow hK
    dsimp only [Q] at hThirdLarge
    dsimp only [K] at hThirdLarge hScaled
    linarith only [hThirdLarge, hBound, hScaled]
  have hDissipationRatioT :
      Tendsto (fun n : ℕ =>
        velocityH3Dissipation3At u (τ n) /
          velocityH3Energy3At u (τ n)) atTop atTop := by
    have hSquareT :
        Tendsto (fun n : ℕ =>
          h3TopCharacteristicFrequencyAt u (τ n) ^ 2) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro M
      let R : ℝ := max M 1
      have hRone : 1 ≤ R := le_max_right M 1
      have hRM : M ≤ R := le_max_left M 1
      have hR2 : M ≤ R ^ 2 := by
        nlinarith only [hRone, hRM, sq_nonneg (R - 1)]
      have hLarge : ∀ᶠ n : ℕ in atTop,
          R ≤ h3TopCharacteristicFrequencyAt u (τ n) :=
        (tendsto_atTop.1 hFrequencyT) R
      filter_upwards [hLarge] with n hn
      have hFreqNonneg : 0 ≤ h3TopCharacteristicFrequencyAt u (τ n) :=
        h3TopCharacteristicFrequencyAt_nonneg u (τ n)
      have hRNonneg : 0 ≤ R := le_trans (by norm_num) hRone
      have hPow : R ^ 2 ≤ h3TopCharacteristicFrequencyAt u (τ n) ^ 2 := by
        gcongr <;> assumption
      exact le_trans hR2 hPow
    have hEq :
        (fun n : ℕ =>
          velocityH3Dissipation3At u (τ n) /
            velocityH3Energy3At u (τ n)) =
        (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n) ^ 2) := by
      funext n
      exact (h3TopCharacteristicFrequencyAt_sq u (τ n)).symm
    rw [hEq]
    exact hSquareT
  exact ⟨i, τ, hNear, hτT, hSourceT, hRatioT,
    hFrequencyT, hDissipationRatioT⟩

/-- A fixed upper bound on the intrinsic top-order characteristic frequency
throughout a strict terminal tail is incompatible with the existing fixed
signed-source nonextension obstruction, and hence implies continuation. -/
theorem h3PathCanonical_extension_of_eventualIntrinsicFrequencyCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hCeiling : ∀ t : ℝ, t ∈ Set.Ioo d T →
      h3TopCharacteristicFrequencyAt u t ≤ K) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨i, τ, hNear, hτT, _hSourceT, _hRatioT,
      hFrequencyT, _hDissipationRatioT⟩ :=
    h3PathCanonical_fixedDirectedSource_intrinsicFrequency_sameSequence
      hH3 hNoExtension hClass hb
  have hLate : ∀ᶠ n : ℕ in atTop, d < τ n :=
    (tendsto_order.1 hτT).1 d hd.2
  have hBound : ∀ᶠ n : ℕ in atTop,
      h3TopCharacteristicFrequencyAt u (τ n) ≤ K := by
    filter_upwards [hLate] with n hn
    exact hCeiling (τ n) ⟨hn, (hNear n).2⟩
  have hLarge : ∀ᶠ n : ℕ in atTop,
      K + 1 ≤ h3TopCharacteristicFrequencyAt u (τ n) :=
    (tendsto_atTop.1 hFrequencyT) (K + 1)
  obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
  linarith only [hnBound, hnLarge]

end
end Euclidean
end Bridge
end PrimeTensor
