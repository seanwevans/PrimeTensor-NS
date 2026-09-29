import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSelectedCeilingRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeActualVorticityRate

/-!
# Actual vorticity on a selected native witness

A raw dissipation ceiling on one specified quantitative native witness
forces a cofinal extraction with divergent normalized minimal vorticity
envelope. The extracted envelope has a linear lower bound and is
approximated at each time by an actual logged vorticity component.
The spatial points for these components can differ from the native
curl-gradient points, and the raw ceiling stays on the original witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A raw ceiling on one fixed native witness forces actual vorticity
component growth on a cofinal extraction of that same witness. The
denominator in the normalized envelope rate retains the original
index `k n`. -/
theorem positiveGrowth_native_actualVorticityExtraction_of_selectedRawCeiling
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
    ∃ k : ℕ → ℕ,
      (∀ n : ℕ, n ≤ k n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k n)) (fun n => y (k n)) ∧
      (∀ n : ℕ,
        (n : ℝ) <
          (1 + |h3MinimalVorticityEnvelopeAt u (τ (k n))|) ^ 2 /
            ((k n : ℝ) + 1)) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + |h3MinimalVorticityEnvelopeAt u (τ (k n))|) ^ 2 /
            ((k n : ℝ) + 1)) atTop atTop ∧
      ∃ z : ℕ → Point3,
        ∀ n : ℕ,
          ((n : ℝ) - 2 <
            |realVorticityX (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ (k n)) (z n)|) ∨
          ((n : ℝ) - 2 <
            |realVorticityY (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ (k n)) (z n)|) ∨
          ((n : ℝ) - 2 <
            |realVorticityZ (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ (k n)) (z n)|) := by
  classical
  have hg : ∀ t : ℝ, t ∈ Set.Ioo b T →
      VorticityEnvelope u (h3MinimalVorticityEnvelopeAt u) t := by
    intro t ht
    have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1) ht.1,
        ht.2⟩
    exact vorticityEnvelope_h3MinimalVorticityEnvelopeAt hH3 ht0
  obtain ⟨k, hk, hNative, hRate, hTop⟩ :=
    positiveGrowth_native_vorticityExtraction_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hg hData hRawCeiling
  have hQuadratic : ∀ n : ℕ,
      (n : ℝ) * ((n : ℝ) + 1) <
        (1 + |h3MinimalVorticityEnvelopeAt u (τ (k n))|) ^ 2 := by
    intro n
    have hDenPos : 0 < (k n : ℝ) + 1 := by positivity
    have hProduct :
        (n : ℝ) * ((k n : ℝ) + 1) <
          (1 + |h3MinimalVorticityEnvelopeAt u (τ (k n))|) ^ 2 :=
      (lt_div_iff₀ hDenPos).mp (hRate n)
    have hCast : (n : ℝ) ≤ (k n : ℝ) := by
      exact_mod_cast hk n
    have hNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hLower :
        (n : ℝ) * ((n : ℝ) + 1) ≤
          (n : ℝ) * ((k n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hNonneg
    exact lt_of_le_of_lt hLower hProduct
  have hLinear :=
    (native_envelopeFactor_growth_to_magnitude
      (h3MinimalVorticityEnvelopeAt u) (fun n => τ (k n))
      hQuadratic).1
  have hWitness : ∀ n : ℕ, ∃ z : Point3,
      ((n : ℝ) - 2 <
        |realVorticityX (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ (k n)) z|) ∨
      ((n : ℝ) - 2 <
        |realVorticityY (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ (k n)) z|) ∨
      ((n : ℝ) - 2 <
        |realVorticityZ (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ (k n)) z|) := by
    intro n
    have ht0 : τ (k n) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1)
        (hNative.1 n).1.1,
        (hNative.1 n).1.2⟩
    have hMinNonneg :
        0 ≤ h3MinimalVorticityEnvelopeAt u (τ (k n)) :=
      h3MinimalVorticityEnvelopeAt_nonneg_of_h3Path hH3 ht0
    have hLinearN := hLinear n
    rw [abs_of_nonneg hMinNonneg] at hLinearN
    have hThreshold :
        h3MinimalVorticityEnvelopeAt u (τ (k n)) - 1 <
          h3MinimalVorticityEnvelopeAt u (τ (k n)) := by
      linarith
    obtain ⟨z, hz⟩ :=
      exists_actualVorticityComponent_gt_of_lt_h3MinimalVorticityEnvelopeAt
        hThreshold
    refine ⟨z, ?_⟩
    rcases hz with hx | hy | hz
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  choose z hz using hWitness
  exact ⟨k, hk, hNative, hRate, hTop, z, hz⟩

end

end Euclidean
end Bridge
end PrimeTensor
