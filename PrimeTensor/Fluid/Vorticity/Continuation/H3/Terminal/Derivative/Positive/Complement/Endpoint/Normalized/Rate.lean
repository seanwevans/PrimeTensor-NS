import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Linear.Obstruction

/-!
# Normalized endpoint rate on relative escape

On either relative-escape orientation, the complete actual-gradient
endpoint factor divided by the original selected index plus one tends
to infinity. This states the rate behind the linear-bound obstruction
without presupposing an upper bound for the vorticity or energy factors.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem originalRate_normalized_atTop
    (k : ℕ → ℕ)
    (F : ℕ → ℝ)
    (hkTop : Tendsto k atTop atTop)
    (hRate : ∀ M : ℝ, 0 < M →
      ∀ᶠ n : ℕ in atTop, M * (k n : ℝ) < F n) :
    Tendsto (fun n : ℕ => F n / ((k n : ℝ) + 1)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro C
  let D : ℝ := max C 0
  let M : ℝ := 2 * D + 1
  have hDNonneg : 0 ≤ D := le_max_right C 0
  have hCLeD : C ≤ D := le_max_left C 0
  have hM : 0 < M := by dsimp [M]; linarith
  have hkLarge : ∀ᶠ n : ℕ in atTop, 1 ≤ k n :=
    hkTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hRate M hM, hkLarge] with n hnRate hnLarge
  have hkCast : (1 : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hnLarge
  have hDen : 0 < (k n : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hDen).2
  have hIndex : (k n : ℝ) + 1 ≤ 2 * (k n : ℝ) := by linarith
  have hFirst : C * ((k n : ℝ) + 1) ≤ D * ((k n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hCLeD (le_of_lt hDen)
  have hSecond : D * ((k n : ℝ) + 1) ≤ D * (2 * (k n : ℝ)) :=
    mul_le_mul_of_nonneg_left hIndex hDNonneg
  have hThird : D * (2 * (k n : ℝ)) ≤ M * (k n : ℝ) := by
    dsimp [M]
    nlinarith [show 0 ≤ (k n : ℝ) by positivity]
  exact (hFirst.trans (hSecond.trans hThird)).trans (le_of_lt hnRate)

/-- Gradient-dominant relative escape forces the actual-gradient endpoint
factor to be superlinear relative to the original selected index. -/
theorem positiveGrowth_gradientRatioEscape_endpoint_normalized_atTop
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
    Tendsto
      (fun n : ℕ =>
        (B * (1 + |g (τ (k n))|) *
          (1 + Real.log (E (τ (k n))))) / ((k n : ℝ) + 1))
      atTop atTop := by
  exact originalRate_normalized_atTop k
    (fun n => B * (1 + |g (τ (k n))|) *
      (1 + Real.log (E (τ (k n))))) hkTop
    (fun M hM =>
      positiveGrowth_gradientRatioEscape_forces_endpointOriginalRate
        hData hCancellation hkTop hRatio hEndpoint M hM)

/-- Curl-dominant relative escape forces the same normalized divergence
of the complete actual-gradient endpoint factor. -/
theorem positiveGrowth_curlRatioEscape_endpoint_normalized_atTop
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
    Tendsto
      (fun n : ℕ =>
        (B * (1 + |g (τ (k n))|) *
          (1 + Real.log (E (τ (k n))))) / ((k n : ℝ) + 1))
      atTop atTop := by
  exact originalRate_normalized_atTop k
    (fun n => B * (1 + |g (τ (k n))|) *
      (1 + Real.log (E (τ (k n))))) hkTop
    (fun M hM =>
      positiveGrowth_curlRatioEscape_forces_endpointOriginalRate
        hData hkTop hRatio hEndpoint M hM)

end

end Euclidean
end Bridge
end PrimeTensor
