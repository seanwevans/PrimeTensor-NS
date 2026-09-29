import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSelectedActualVorticityRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeActualVorticityMaxRate

/-!
# Normalized actual vorticity on a selected native witness

The minimal common vorticity envelope can be approximated at each
selected time by one actual component at some spatial point. Selecting
those points before taking the maximum of the three components gives
a physical amplitude whose normalized squared rate diverges. The
component attaining the maximum may change with the index.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A component within one unit of a nonnegative minimal envelope
controls its squared offset by a factor of four. -/
theorem minimalEnvelope_square_le_four_actualSquare
    {M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hApprox : M - 1 < A) :
    (1 + M) ^ 2 ≤ 4 * (1 + A) ^ 2 := by
  have hLinear : 1 + M ≤ 2 * (1 + A) := by linarith
  have hSquare :
      (1 + M) ^ 2 ≤ (2 * (1 + A)) ^ 2 :=
    (sq_le_sq₀ (by linarith : 0 ≤ 1 + M)
      (by linarith : 0 ≤ 2 * (1 + A))).2 hLinear
  nlinarith

/-- A raw ceiling on one supplied native witness selects actual
vorticity points where the squared normalized component maximum
diverges. The denominator retains the original witness index `k n`;
the ceiling is not asserted on the extracted witness. -/
theorem positiveGrowth_native_actualVorticityRatio_of_selectedRawCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hRawCeiling : H3TerminalNativeRawSubexponentialCeilingOnWitness u τ) :
    ∃ k : ℕ → ℕ, ∃ z : ℕ → Point3,
      (∀ n : ℕ, n ≤ k n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k n)) (fun n => y (k n)) ∧
      (∀ n : ℕ,
        h3MinimalVorticityEnvelopeAt u (τ (k n)) - 1 <
          h3NativeActualVorticityComponentMaxAt u (τ (k n)) (z n)) ∧
      (∀ n : ℕ,
        (1 + |h3MinimalVorticityEnvelopeAt u (τ (k n))|) ^ 2 /
            ((k n : ℝ) + 1) ≤
          4 *
            ((1 + h3NativeActualVorticityComponentMaxAt u
              (τ (k n)) (z n)) ^ 2 / ((k n : ℝ) + 1))) ∧
      (∀ n : ℕ,
        (n : ℝ) / 4 <
          (1 + h3NativeActualVorticityComponentMaxAt u
            (τ (k n)) (z n)) ^ 2 / ((k n : ℝ) + 1)) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + h3NativeActualVorticityComponentMaxAt u
            (τ (k n)) (z n)) ^ 2 / ((k n : ℝ) + 1))
        atTop atTop := by
  classical
  have hg : ∀ t : ℝ, t ∈ Set.Ioo b T →
      VorticityEnvelope u (h3MinimalVorticityEnvelopeAt u) t := by
    intro t ht
    have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1) ht.1,
        ht.2⟩
    exact vorticityEnvelope_h3MinimalVorticityEnvelopeAt hH3 ht0
  obtain ⟨k, hk, hNative, hMinRate, hMinTop⟩ :=
    positiveGrowth_native_vorticityExtraction_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hg hData hRawCeiling
  have hWitness : ∀ n : ℕ, ∃ z : Point3,
      h3MinimalVorticityEnvelopeAt u (τ (k n)) - 1 <
        h3NativeActualVorticityComponentMaxAt u (τ (k n)) z := by
    intro n
    have hThreshold :
        h3MinimalVorticityEnvelopeAt u (τ (k n)) - 1 <
          h3MinimalVorticityEnvelopeAt u (τ (k n)) := by
      linarith
    obtain ⟨z, hz⟩ :=
      exists_actualVorticityComponent_gt_of_lt_h3MinimalVorticityEnvelopeAt
        hThreshold
    refine ⟨z, ?_⟩
    dsimp only [h3NativeActualVorticityComponentMaxAt]
    rcases hz with hx | hy | hz
    · exact lt_of_lt_of_le hx (le_max_left _ _)
    · exact lt_of_lt_of_le hy
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact lt_of_lt_of_le hz
        (le_trans (le_max_right _ _) (le_max_right _ _))
  choose z hApprox using hWitness
  have hCompare : ∀ n : ℕ,
      (1 + |h3MinimalVorticityEnvelopeAt u (τ (k n))|) ^ 2 /
          ((k n : ℝ) + 1) ≤
        4 *
          ((1 + h3NativeActualVorticityComponentMaxAt u
            (τ (k n)) (z n)) ^ 2 / ((k n : ℝ) + 1)) := by
    intro n
    have ht0 : τ (k n) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1)
        (hNative.1 n).1.1, (hNative.1 n).1.2⟩
    have hMinNonneg :
        0 ≤ h3MinimalVorticityEnvelopeAt u (τ (k n)) :=
      h3MinimalVorticityEnvelopeAt_nonneg_of_h3Path hH3 ht0
    have hMaxNonneg :
        0 ≤ h3NativeActualVorticityComponentMaxAt u
          (τ (k n)) (z n) := by
      unfold h3NativeActualVorticityComponentMaxAt
      exact (abs_nonneg _).trans (le_max_left _ _)
    have hSquare :=
      minimalEnvelope_square_le_four_actualSquare
        hMinNonneg hMaxNonneg (hApprox n)
    rw [abs_of_nonneg hMinNonneg]
    have hDiv := div_le_div_of_nonneg_right hSquare
      (show 0 ≤ (k n : ℝ) + 1 by positivity)
    calc
      (1 + h3MinimalVorticityEnvelopeAt u (τ (k n))) ^ 2 /
          ((k n : ℝ) + 1) ≤
          (4 * (1 + h3NativeActualVorticityComponentMaxAt u
            (τ (k n)) (z n)) ^ 2) / ((k n : ℝ) + 1) := hDiv
      _ = 4 *
          ((1 + h3NativeActualVorticityComponentMaxAt u
            (τ (k n)) (z n)) ^ 2 / ((k n : ℝ) + 1)) := by ring
  have hQuarter : ∀ n : ℕ,
      (n : ℝ) / 4 <
        (1 + h3NativeActualVorticityComponentMaxAt u
          (τ (k n)) (z n)) ^ 2 / ((k n : ℝ) + 1) := by
    intro n
    linarith [hMinRate n, hCompare n]
  have hTop :
      Tendsto
        (fun n : ℕ =>
          (1 + h3NativeActualVorticityComponentMaxAt u
            (τ (k n)) (z n)) ^ 2 / ((k n : ℝ) + 1))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro C
    filter_upwards [hMinTop.eventually (eventually_ge_atTop (4 * C))]
      with n hn
    linarith [hCompare n]
  exact ⟨k, z, hk, hNative, hApprox, hCompare, hQuarter, hTop⟩

end

end Euclidean
end Bridge
end PrimeTensor
