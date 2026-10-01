import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Canonical.Endpoint.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.BKM.Frequency.Linear.Lower.Bound

/-!
# Vorticity envelope on the quantitative native witness

Under hypothetical nonextension, the BKM frequency estimate applies
at every sufficiently late positive-growth time. The quantitative
native witness has positive H³ energy derivative, tends to the terminal
time, and carries diverging top characteristic frequency. Therefore
every vorticity envelope on the chosen tail diverges along that same
native witness. No replacement sequence is needed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Every vorticity envelope diverges on the specified quantitative
native curl-gradient witness under hypothetical nonextension. -/
theorem positiveGrowth_nativeWitness_vorticityEnvelope_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
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
        u b T p sCurl sGradient τ y) :
    Tendsto (fun n : ℕ => |g (τ n)|) atTop atTop := by
  obtain ⟨c, hc, hLinear⟩ :=
    exists_terminalTail_positiveGrowth_characteristicFrequency_linear_lt_vorticityEnvelope_of_noH3PathExtension
      hH3 hNoExtension hClass hb hg
  rcases hData with ⟨hAt, hTau, _, _, _, hFreq, _, _, _⟩
  have hEventuallyTail : ∀ᶠ n : ℕ in atTop, c < τ n :=
    (tendsto_order.1 hTau).1 c hc.2
  let D : ℝ :=
    (((4 + 3 * velocityH3Energy0At u b) * 4422 *
        (h3BKMCanonicalSelectedLogGradientConstant
          (Real.sqrt (velocityH3Energy0At u b)) + 1)) *
      (((4 + 3 * velocityH3Energy0At u b) *
          (velocityH3Energy0At u b + 1)) + 7))
  have hEnergy0 : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hBNonneg :
      0 ≤ h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u b)) :=
    h3BKMCanonicalSelectedLogGradientConstant_nonneg
      (Real.sqrt_nonneg _)
  have hCPos : 0 < 4 + 3 * velocityH3Energy0At u b := by
    linarith
  have hAnchorPos : 0 < velocityH3Energy0At u b + 1 := by
    linarith
  have hBPos :
      0 < h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u b)) + 1 := by
    linarith
  have hLastPos :
      0 < (4 + 3 * velocityH3Energy0At u b) *
          (velocityH3Energy0At u b + 1) + 7 := by
    have hProduct := mul_pos hCPos hAnchorPos
    linarith
  have hDPos : 0 < D := by
    dsimp only [D]
    exact mul_pos
      (mul_pos (mul_pos hCPos (by norm_num)) hBPos)
      hLastPos
  refine tendsto_atTop.2 ?_
  intro M
  by_cases hM : M ≤ 0
  · exact Eventually.of_forall (fun n =>
      hM.trans (abs_nonneg (g (τ n))))
  · have hMPos : 0 < M := lt_of_not_ge hM
    have hFreqLarge : ∀ᶠ n : ℕ in atTop,
        D * (M + 2) ≤ h3TopCharacteristicFrequencyAt u (τ n) :=
      hFreq.eventually (eventually_ge_atTop (D * (M + 2)))
    filter_upwards [hEventuallyTail, hFreqLarge] with n hTail hLarge
    have hAtTail : τ n ∈ Set.Ioo c T :=
      ⟨hTail, (hAt n).1.2⟩
    have hDerivative : 0 < deriv (velocityH3EnergyAt u) (τ n) := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      exact lt_of_le_of_lt hn (hAt n).2.2.1
    have hEnvelope :
        2 * h3TopCharacteristicFrequencyAt u (τ n) / D <
          1 + |g (τ n)| := by
      dsimp only [D]
      exact hLinear (τ n) hAtTail hDerivative
    have hThreshold :
        M + 1 < 2 * h3TopCharacteristicFrequencyAt u (τ n) / D := by
      apply (lt_div_iff₀ hDPos).2
      have hMargin : 0 < D * (M + 3) :=
        mul_pos hDPos (by linarith)
      nlinarith
    exact le_of_lt (by linarith : M < |g (τ n)|)

end

end Euclidean
end Bridge
end PrimeTensor
