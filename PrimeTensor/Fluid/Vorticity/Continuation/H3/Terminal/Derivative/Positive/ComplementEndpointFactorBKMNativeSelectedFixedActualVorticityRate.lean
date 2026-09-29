import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSelectedActualVorticityRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFixedActualVorticityRate

/-!
# Fixed actual vorticity component on a selected native witness

The selected raw ceiling first extracts divergent normalized minimal
vorticity and actual component growth. A second cofinal extraction
fixes one of the three logged vorticity components. Both extractions
preserve the native cascade, and the normalized envelope rate keeps
the original index in its denominator. The ceiling remains an
assumption only on the supplied, unextracted native witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- One selected raw ceiling fixes an actual vorticity coordinate along
a cofinal native extraction. Its spatial points may differ from the
native curl-gradient points. -/
theorem positiveGrowth_native_fixedActualVorticityExtraction_of_selectedRawCeiling
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
        (n : ℝ) <
          (1 + |h3MinimalVorticityEnvelopeAt u (τ (m n))|) ^ 2 /
            ((m n : ℝ) + 1)) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + |h3MinimalVorticityEnvelopeAt u (τ (m n))|) ^ 2 /
            ((m n : ℝ) + 1)) atTop atTop ∧
      (∀ n : ℕ,
        (n : ℝ) - 2 <
          |h3NativeActualVorticityComponentAt u i
            (τ (m n)) (z n)|) ∧
      Tendsto
        (fun n : ℕ =>
          |h3NativeActualVorticityComponentAt u i
            (τ (m n)) (z n)|) atTop atTop := by
  classical
  obtain ⟨k, hk, _hNative, hRatio, hRatioTop, z, hComponent⟩ :=
    positiveGrowth_native_actualVorticityExtraction_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hData hRawCeiling
  obtain ⟨i, l, hl, hFixed, hFixedTop⟩ :=
    native_actualVorticity_fixedComponent_extraction
      u (fun n => τ (k n)) z hComponent
  let m : ℕ → ℕ := fun n => k (l n)
  have hm : ∀ n : ℕ, n ≤ m n := by
    intro n
    exact (hl n).trans (hk (l n))
  have hlTop : Tendsto l atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hl n)
  have hExtractedRatio : ∀ n : ℕ,
      (n : ℝ) <
        (1 + |h3MinimalVorticityEnvelopeAt u (τ (m n))|) ^ 2 /
          ((m n : ℝ) + 1) := by
    intro n
    have hCast : (n : ℝ) ≤ (l n : ℝ) := by
      exact_mod_cast hl n
    exact lt_of_le_of_lt hCast (hRatio (l n))
  have hExtractedRatioTop :
      Tendsto
        (fun n : ℕ =>
          (1 + |h3MinimalVorticityEnvelopeAt u (τ (m n))|) ^ 2 /
            ((m n : ℝ) + 1)) atTop atTop :=
    hRatioTop.comp hlTop
  exact ⟨i, m, (fun n => z (l n)), hm,
    positiveGrowth_quantitativeNativeData_comp_cofinal hData hm,
    hExtractedRatio, hExtractedRatioTop, hFixed, hFixedTop⟩

end

end Euclidean
end Bridge
end PrimeTensor
