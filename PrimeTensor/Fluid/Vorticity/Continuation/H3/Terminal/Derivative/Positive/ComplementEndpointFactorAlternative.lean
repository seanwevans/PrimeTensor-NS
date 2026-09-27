import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorMaxRate

/-!
# Eventual factor alternative on relative escape

The maximum of the two canonical BKM factors has a squared rate above
every fixed multiple of the original selected index. Hence at every
sufficiently late extracted index, one of the two factors crosses that
threshold. The factor can vary with the index; no persistent orientation
of this new factor alternative is claimed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem maxSquareRate_eventually_factorAlternative
    (k : ℕ → ℕ)
    (A L : ℕ → ℝ)
    (hMax :
      Tendsto
        (fun n : ℕ => (max (A n) (L n)) ^ 2 / ((k n : ℝ) + 1))
        atTop atTop)
    (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * ((k n : ℝ) + 1) < (A n) ^ 2 ∨
        C * ((k n : ℝ) + 1) < (L n) ^ 2 := by
  have hLarge : ∀ᶠ n : ℕ in atTop,
      C < (max (A n) (L n)) ^ 2 / ((k n : ℝ) + 1) :=
    hMax.eventually (eventually_gt_atTop C)
  filter_upwards [hLarge] with n hn
  have hDen : 0 < (k n : ℝ) + 1 := by positivity
  have hSquare :
      C * ((k n : ℝ) + 1) < (max (A n) (L n)) ^ 2 :=
    (lt_div_iff₀ hDen).1 hn
  rcases le_total (A n) (L n) with hAL | hLA
  · right
    simpa only [max_eq_right hAL] using hSquare
  · left
    simpa only [max_eq_left hLA] using hSquare

/-- In gradient-dominant relative escape, every fixed square-root
threshold is eventually exceeded by at least one canonical BKM factor. -/
theorem positiveGrowth_gradientRatioEscape_endpoint_factorAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
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
              u p sGradient (τ (k n)) (y (k n)))
    (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * ((k n : ℝ) + 1) < (1 + |g (τ (k n))|) ^ 2 ∨
        C * ((k n : ℝ) + 1) <
          (1 + Real.log (velocityH3EnergyAt u (τ (k n)))) ^ 2 := by
  exact maxSquareRate_eventually_factorAlternative k
    (fun n => 1 + |g (τ (k n))|)
    (fun n => 1 + Real.log (velocityH3EnergyAt u (τ (k n))))
    (positiveGrowth_gradientRatioEscape_canonicalEndpoint_factorMaxRate
      hH3 hClass hb hg hData hCancellation hkTop hRatio) C

/-- Curl-dominant relative escape has the same eventual factor
alternative at every fixed original-index threshold. -/
theorem positiveGrowth_curlRatioEscape_endpoint_factorAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
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
              u p sGradient (τ (k n)) (y (k n)))
    (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * ((k n : ℝ) + 1) < (1 + |g (τ (k n))|) ^ 2 ∨
        C * ((k n : ℝ) + 1) <
          (1 + Real.log (velocityH3EnergyAt u (τ (k n)))) ^ 2 := by
  exact maxSquareRate_eventually_factorAlternative k
    (fun n => 1 + |g (τ (k n))|)
    (fun n => 1 + Real.log (velocityH3EnergyAt u (τ (k n))))
    (positiveGrowth_curlRatioEscape_canonicalEndpoint_factorMaxRate
      hH3 hClass hb hg hData hkTop hRatio) C

end

end Euclidean
end Bridge
end PrimeTensor
