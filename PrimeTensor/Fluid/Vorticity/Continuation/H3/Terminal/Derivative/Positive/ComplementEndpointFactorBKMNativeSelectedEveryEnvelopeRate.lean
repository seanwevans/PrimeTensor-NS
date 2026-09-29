import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSelectedFixedActualVorticityRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFixedActualVorticityEnvelopeEscape

/-!
# Every envelope on a selected native sequence

One fixed-witness raw dissipation ceiling selects a native subsequence
and a fixed actual vorticity component. The points and times are chosen
before an admissible envelope is specified. Each envelope dominates
that component and the minimal common envelope, so every envelope
inherits both linear growth and the divergent normalized ratio on
the same subsequence. The raw ceiling is attached only to the original
native sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The canonical minimal envelope is below any common vorticity
envelope on a strict preterminal slice. -/
theorem h3MinimalVorticityEnvelopeAt_le_commonEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ} {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t) :
    h3MinimalVorticityEnvelopeAt u t ≤ g t := by
  unfold h3MinimalVorticityEnvelopeAt
  exact csInf_le
    (h3VorticityCommonUpperBoundsAt_bddBelow u t) hEnvelope

/-- A ceiling on one specified native witness gives a cofinal native
sequence whose fixed actual component and every admissible envelope
grow together. The normalized rates use the original index `m n`.
The universal quantifier over envelopes is after the sequence choice. -/
theorem positiveGrowth_native_everyEnvelopeExtraction_of_selectedRawCeiling
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
    ∃ i : Fin 3, ∃ m : ℕ → ℕ, ∃ z : ℕ → Point3,
      (∀ n : ℕ, n ≤ m n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (m n)) (fun n => y (m n)) ∧
      (∀ n : ℕ,
        (n : ℝ) - 2 <
          |h3NativeActualVorticityComponentAt u i
            (τ (m n)) (z n)|) ∧
      Tendsto
        (fun n : ℕ =>
          |h3NativeActualVorticityComponentAt u i
            (τ (m n)) (z n)|) atTop atTop ∧
      ∀ g : ℝ → ℝ,
        (∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t) →
          (∀ n : ℕ, (n : ℝ) - 2 < g (τ (m n))) ∧
          Tendsto (fun n : ℕ => g (τ (m n))) atTop atTop ∧
          (∀ n : ℕ,
            (n : ℝ) <
              (1 + |g (τ (m n))|) ^ 2 / ((m n : ℝ) + 1)) ∧
          Tendsto
            (fun n : ℕ =>
              (1 + |g (τ (m n))|) ^ 2 / ((m n : ℝ) + 1))
            atTop atTop := by
  obtain ⟨i, m, z, hm, hNative, hMinRate, hMinTop,
    hFixed, hFixedTop⟩ :=
    positiveGrowth_native_fixedActualVorticityExtraction_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hData hRawCeiling
  refine ⟨i, m, z, hm, hNative, hFixed, hFixedTop, ?_⟩
  intro g hg
  have hAt : ∀ n : ℕ,
      |h3NativeActualVorticityComponentAt u i
        (τ (m n)) (z n)| ≤ g (τ (m n)) := by
    intro n
    exact h3NativeActualVorticityComponentAt_le_vorticityEnvelope
      (hg (τ (m n)) (hNative.1 n).1) i (z n)
  have hLinear : ∀ n : ℕ, (n : ℝ) - 2 < g (τ (m n)) := by
    intro n
    exact lt_of_lt_of_le (hFixed n) (hAt n)
  have hEnvelopeTop : Tendsto (fun n : ℕ => g (τ (m n))) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro C
    filter_upwards [hFixedTop.eventually (eventually_ge_atTop C)] with n hn
    exact le_trans hn (hAt n)
  have hRatioLe : ∀ n : ℕ,
      (1 + |h3MinimalVorticityEnvelopeAt u (τ (m n))|) ^ 2 /
          ((m n : ℝ) + 1) ≤
        (1 + |g (τ (m n))|) ^ 2 / ((m n : ℝ) + 1) := by
    intro n
    have ht0 : τ (m n) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1)
        (hNative.1 n).1.1, (hNative.1 n).1.2⟩
    have hMinNonneg :
        0 ≤ h3MinimalVorticityEnvelopeAt u (τ (m n)) :=
      h3MinimalVorticityEnvelopeAt_nonneg_of_h3Path hH3 ht0
    have hMinLe :
        h3MinimalVorticityEnvelopeAt u (τ (m n)) ≤ g (τ (m n)) :=
      h3MinimalVorticityEnvelopeAt_le_commonEnvelope
        (hg (τ (m n)) (hNative.1 n).1)
    have hGNonneg : 0 ≤ g (τ (m n)) := hMinNonneg.trans hMinLe
    have hSquare :
        (1 + |h3MinimalVorticityEnvelopeAt u (τ (m n))|) ^ 2 ≤
          (1 + |g (τ (m n))|) ^ 2 := by
      rw [abs_of_nonneg hMinNonneg, abs_of_nonneg hGNonneg]
      exact (sq_le_sq₀ (by linarith :
          0 ≤ 1 + h3MinimalVorticityEnvelopeAt u (τ (m n)))
        (by linarith : 0 ≤ 1 + g (τ (m n)))).2 (by linarith)
    exact div_le_div_of_nonneg_right hSquare (by positivity)
  have hRate : ∀ n : ℕ,
      (n : ℝ) <
        (1 + |g (τ (m n))|) ^ 2 / ((m n : ℝ) + 1) := by
    intro n
    exact lt_of_lt_of_le (hMinRate n) (hRatioLe n)
  have hRateTop :
      Tendsto
        (fun n : ℕ =>
          (1 + |g (τ (m n))|) ^ 2 / ((m n : ℝ) + 1))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro C
    filter_upwards [hMinTop.eventually (eventually_ge_atTop C)] with n hn
    exact le_trans hn (hRatioLe n)
  exact ⟨hLinear, hEnvelopeTop, hRate, hRateTop⟩

end

end Euclidean
end Bridge
end PrimeTensor
