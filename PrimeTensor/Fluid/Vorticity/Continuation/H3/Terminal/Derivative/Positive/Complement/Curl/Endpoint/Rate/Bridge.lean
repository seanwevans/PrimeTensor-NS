import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Rate.Bridge

/-!
# Curl-dominant escape against the actual-gradient endpoint factor

The correctly signed curl log is the difference between the selected
and complementary actual velocity derivatives. The BKM endpoint bounds
both derivatives, and hence bounds either orientation of that signed
curl log by twice its common endpoint factor. Combined with the native
original-index escape theorem, this transfers curl-dominant growth to
the same endpoint factor as in the gradient-dominant branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Two actual-gradient endpoint estimates bound the correctly signed
curl logarithm, in either selected-gradient orientation. -/
theorem positiveGrowth_signedCurl_le_two_endpointFactor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {g E : ℝ → ℝ}
    {B : ℝ}
    (hEndpoint : ActualVelocityGradientLogBoundFrom u a T g E B)
    (p : H3TerminalCurlGradientPair)
    (sGradient : H3TerminalOrientation)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (x : Point3) :
    h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient t x ≤
      2 * (B * (1 + |g t|) * (1 + Real.log (E t))) := by
  have hIdentity := logValue_nativeComplement_eq_gradient_sub_signedCurl
    u p t x
  rw [logValue_h3TerminalNativeComplementGradientForPair,
    logValue_h3TerminalNativeGradientForPair] at hIdentity
  have hSigned :
      h3TerminalSelectedSignedNativeCurlLog u p t x =
        h3TerminalGradientFieldForPair u p t x -
          h3TerminalComplementGradientFieldForPair u p t x := by
    linarith [hIdentity]
  have hOriented :
      h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient t x ≤
        |h3TerminalGradientFieldForPair u p t x -
          h3TerminalComplementGradientFieldForPair u p t x| := by
    unfold h3TerminalOrientedSelectedSignedCurlLogForPair
    rw [hSigned]
    exact h3TerminalOrientedValue_le_abs sGradient _
  have hTriangle :
      |h3TerminalGradientFieldForPair u p t x -
          h3TerminalComplementGradientFieldForPair u p t x| ≤
        |h3TerminalGradientFieldForPair u p t x| +
          |h3TerminalComplementGradientFieldForPair u p t x| := by
    simpa [sub_eq_add_neg] using
      (abs_add_le
        (h3TerminalGradientFieldForPair u p t x)
        (-h3TerminalComplementGradientFieldForPair u p t x))
  have hSelected :=
    hEndpoint t ht
      (h3TerminalGradientDerivativeAxisForPair p)
      (h3TerminalGradientComponentAxisForPair p) x
  change 1 + |h3TerminalGradientFieldForPair u p t x| ≤
    B * (1 + |g t|) * (1 + Real.log (E t)) at hSelected
  have hComplement :=
    hEndpoint t ht
      (h3TerminalComplementDerivativeAxisForPair p)
      (h3TerminalComplementComponentAxisForPair p) x
  change 1 + |h3TerminalComplementGradientFieldForPair u p t x| ≤
    B * (1 + |g t|) * (1 + Real.log (E t)) at hComplement
  linarith

/-- Curl-dominant relative escape makes the actual-gradient endpoint
factor exceed every positive multiple of the original selected index. -/
theorem positiveGrowth_curlRatioEscape_forces_endpointOriginalRate
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
    (hEndpoint : ActualVelocityGradientLogBoundFrom u a T g E B)
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
        B * (1 + |g (τ (k n))|) *
          (1 + Real.log (E (τ (k n)))) := by
  have hGrowth :=
    positiveGrowth_curlRatioEscape_nativeScale_originalIndex
      hData hkTop hRatio (2 * M) (by linarith)
  filter_upwards [hGrowth] with n hn
  have hBound := positiveGrowth_signedCurl_le_two_endpointFactor
    hEndpoint p sGradient (τ (k n)) (hData.1 (k n)).1 (y (k n))
  nlinarith

end

end Euclidean
end Bridge
end PrimeTensor
