import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Curl.Endpoint.Rate.Bridge

/-!
# Linear endpoint bounds exclude relative escape

Both orientations of relative escape force the actual-gradient endpoint
factor above every fixed multiple of the original selected index. An
eventual linear upper bound for that same factor on the extracted sequence
therefore rules out either orientation. The linear bound is an additional
hypothesis; the available endpoint interface does not establish it.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem originalRate_not_eventually_linear
    (k : ℕ → ℕ)
    (F : ℕ → ℝ)
    (hkTop : Tendsto k atTop atTop)
    (hRate : ∀ M : ℝ, 0 < M →
      ∀ᶠ n : ℕ in atTop, M * (k n : ℝ) < F n) :
    ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      F n ≤ C * ((k n : ℝ) + 1) := by
  rintro ⟨C, hLinear⟩
  let D : ℝ := max C 0
  let M : ℝ := 2 * D + 1
  have hDNonneg : 0 ≤ D := le_max_right C 0
  have hCLeD : C ≤ D := le_max_left C 0
  have hM : 0 < M := by dsimp [M]; linarith
  have hkLarge : ∀ᶠ n : ℕ in atTop, 1 ≤ k n :=
    hkTop.eventually (eventually_ge_atTop 1)
  obtain ⟨n, ⟨hnRate, hnLinear⟩, hnLarge⟩ :=
    (((hRate M hM).and hLinear).and hkLarge).exists
  have hkCast : (1 : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hnLarge
  have hIndex : (k n : ℝ) + 1 ≤ 2 * (k n : ℝ) := by linarith
  have hFirst : C * ((k n : ℝ) + 1) ≤ D * ((k n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hCLeD (by positivity)
  have hSecond : D * ((k n : ℝ) + 1) ≤ D * (2 * (k n : ℝ)) :=
    mul_le_mul_of_nonneg_left hIndex hDNonneg
  have hThird : D * (2 * (k n : ℝ)) ≤ M * (k n : ℝ) := by
    dsimp [M]
    nlinarith [show 0 ≤ (k n : ℝ) by positivity]
  have hUpper : F n ≤ M * (k n : ℝ) :=
    hnLinear.trans (hFirst.trans (hSecond.trans hThird))
  exact (not_lt_of_ge hUpper) hnRate

/-- A gradient-dominant relative escape cannot coexist with an eventual
linear bound on the complete actual-gradient endpoint factor along the
same original-index subsequence. -/
theorem positiveGrowth_gradientRatioEscape_endpoint_not_linear
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g E : ℝ → ℝ}
    {B : ℝ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
    (hEndpoint : ActualVelocityGradientLogBoundFrom u a T g E B) :
    ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      B * (1 + |g (τ (k n))|) *
          (1 + Real.log (E (τ (k n)))) ≤
        C * ((k n : ℝ) + 1) := by
  exact originalRate_not_eventually_linear k
    (fun n => B * (1 + |g (τ (k n))|) *
      (1 + Real.log (E (τ (k n))))) hkTop
    (fun M hM =>
      positiveGrowth_gradientRatioEscape_forces_endpointOriginalRate
        hData hCancellation hkTop hRatio hEndpoint M hM)

/-- A curl-dominant relative escape has the same obstruction to an
eventual linear bound on the complete actual-gradient endpoint factor. -/
theorem positiveGrowth_curlRatioEscape_endpoint_not_linear
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g E : ℝ → ℝ}
    {B : ℝ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))
    (hEndpoint : ActualVelocityGradientLogBoundFrom u a T g E B) :
    ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      B * (1 + |g (τ (k n))|) *
          (1 + Real.log (E (τ (k n)))) ≤
        C * ((k n : ℝ) + 1) := by
  exact originalRate_not_eventually_linear k
    (fun n => B * (1 + |g (τ (k n))|) *
      (1 + Real.log (E (τ (k n))))) hkTop
    (fun M hM =>
      positiveGrowth_curlRatioEscape_forces_endpointOriginalRate
        hData hkTop hRatio hEndpoint M hM)

end

end Euclidean
end Bridge
end PrimeTensor
