import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Envelope.Synchronization

/-!
# Logarithmic energy factor on the relative-escape witness

The quantitative native witness has H³ energy tending to infinity.
Logarithm preserves this divergence after cofinal extraction. Thus
both nonconstant factors of the canonical BKM endpoint product diverge
on the same relative-escape subsequence. Their individual rates relative
to the original selected index are not asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem one_add_log_atTop_of_energy_atTop
    (E : ℕ → ℝ)
    (hE : Tendsto E atTop atTop) :
    Tendsto (fun n : ℕ => 1 + Real.log (E n)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  have hLarge : ∀ᶠ n : ℕ in atTop, Real.exp M ≤ E n :=
    hE.eventually (eventually_ge_atTop (Real.exp M))
  filter_upwards [hLarge] with n hn
  have hLog : M ≤ Real.log (E n) := by
    rw [← Real.log_exp M]
    exact Real.log_le_log (Real.exp_pos M) hn
  linarith

/-- The actual H³ logarithmic energy factor diverges on any cofinal
extraction of the quantitative native witness. -/
theorem positiveGrowth_relativeWitness_logEnergyFactor_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        1 + Real.log (velocityH3EnergyAt u (τ (k n))))
      atTop atTop := by
  have hEnergy :
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (τ n))
        atTop atTop := by
    rcases hData with ⟨_, _, hEnergy, _, _, _, _, _, _⟩
    exact hEnergy
  exact one_add_log_atTop_of_energy_atTop _ (hEnergy.comp hkTop)

/-- Gradient-dominant relative escape makes both BKM factors diverge,
while their canonical product has a superlinear original-index rate. -/
theorem positiveGrowth_gradientRatioEscape_canonicalEndpoint_logFactors
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
        (fun n : ℕ =>
          1 + Real.log (velocityH3EnergyAt u (τ (k n))))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt (velocityH3Energy0At u b)) *
            (1 + |g (τ (k n))|) *
            (1 + Real.log (velocityH3EnergyAt u (τ (k n))))) /
              ((k n : ℝ) + 1))
        atTop atTop := by
  have hPrevious :=
    positiveGrowth_gradientRatioEscape_canonicalEndpoint_scalarDivergence
      hH3 hNoExtension hClass hb hg hData hCancellation hkTop hRatio
  exact ⟨hPrevious.1,
    positiveGrowth_relativeWitness_logEnergyFactor_atTop hData hkTop,
    hPrevious.2.2⟩

/-- Curl-dominant relative escape has the same two divergent BKM
factors and superlinear canonical product on its extracted witness. -/
theorem positiveGrowth_curlRatioEscape_canonicalEndpoint_logFactors
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
        (fun n : ℕ =>
          1 + Real.log (velocityH3EnergyAt u (τ (k n))))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt (velocityH3Energy0At u b)) *
            (1 + |g (τ (k n))|) *
            (1 + Real.log (velocityH3EnergyAt u (τ (k n))))) /
              ((k n : ℝ) + 1))
        atTop atTop := by
  have hPrevious :=
    positiveGrowth_curlRatioEscape_canonicalEndpoint_scalarDivergence
      hH3 hNoExtension hClass hb hg hData hkTop hRatio
  exact ⟨hPrevious.1,
    positiveGrowth_relativeWitness_logEnergyFactor_atTop hData hkTop,
    hPrevious.2.2⟩

end

end Euclidean
end Bridge
end PrimeTensor
