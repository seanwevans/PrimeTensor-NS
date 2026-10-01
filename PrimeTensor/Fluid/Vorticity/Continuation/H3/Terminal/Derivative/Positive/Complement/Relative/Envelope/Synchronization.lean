import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Native.Vorticity.Synchronization

/-!
# Canonical endpoint and scalar limits on one relative-escape subsequence

The quantitative native witness already carries H³ energy divergence.
Under hypothetical nonextension its vorticity envelope also diverges
on that witness. Cofinal extraction preserves both limits. In either
relative-escape orientation, the canonical BKM endpoint rate is thus
synchronized with both scalar divergences on the very same indices.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Cofinal extraction preserves H³ energy and vorticity-envelope
divergence on the quantitative native witness. -/
theorem positiveGrowth_relativeWitness_scalarDivergence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop) :
    Tendsto (fun n : ℕ => |g (τ (k n))|) atTop atTop ∧
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (τ (k n)))
        atTop atTop := by
  have hEnvelope :=
    positiveGrowth_nativeWitness_vorticityEnvelope_atTop
      hH3 hNoExtension hClass hb hg hData
  have hEnergy :
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (τ n))
        atTop atTop := by
    rcases hData with ⟨_, _, hEnergy, _, _, _, _, _, _⟩
    exact hEnergy
  exact ⟨hEnvelope.comp hkTop, hEnergy.comp hkTop⟩

/-- Gradient-dominant relative escape synchronizes scalar divergence
with superlinear growth of the canonical actual-gradient endpoint factor. -/
theorem positiveGrowth_gradientRatioEscape_canonicalEndpoint_scalarDivergence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))) :
    Tendsto (fun n : ℕ => |g (τ (k n))|) atTop atTop ∧
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (τ (k n)))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt (velocityH3Energy0At u b)) *
            (1 + |g (τ (k n))|) *
            (1 + Real.log (velocityH3EnergyAt u (τ (k n))))) /
              ((k n : ℝ) + 1))
        atTop atTop := by
  obtain ⟨hEnvelope, hEnergy⟩ :=
    positiveGrowth_relativeWitness_scalarDivergence
      hH3 hNoExtension hClass hb hg hData hkTop
  exact ⟨hEnvelope, hEnergy,
    positiveGrowth_gradientRatioEscape_canonicalEndpoint_normalized_atTop
      hH3 hClass hb hg hData hCancellation hkTop hRatio⟩

/-- Curl-dominant relative escape has the same three synchronized
divergences on the extracted original-index subsequence. -/
theorem positiveGrowth_curlRatioEscape_canonicalEndpoint_scalarDivergence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))) :
    Tendsto (fun n : ℕ => |g (τ (k n))|) atTop atTop ∧
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (τ (k n)))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt (velocityH3Energy0At u b)) *
            (1 + |g (τ (k n))|) *
            (1 + Real.log (velocityH3EnergyAt u (τ (k n))))) /
              ((k n : ℝ) + 1))
        atTop atTop := by
  obtain ⟨hEnvelope, hEnergy⟩ :=
    positiveGrowth_relativeWitness_scalarDivergence
      hH3 hNoExtension hClass hb hg hData hkTop
  exact ⟨hEnvelope, hEnergy,
    positiveGrowth_curlRatioEscape_canonicalEndpoint_normalized_atTop
      hH3 hClass hb hg hData hkTop hRatio⟩

end

end Euclidean
end Bridge
end PrimeTensor
