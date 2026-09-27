import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeBothNativeScale
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Logarithmic.Interface
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualStrongH3EndpointContradiction

/-!
# A quantitative native witness against the actual-gradient endpoint bound

The native selected-gradient logarithm is exactly one actual spatial
derivative of the logged velocity. Its orientation is bounded by its
absolute value. Thus any actual-gradient BKM endpoint bound must have
its right-hand side above the index on the positive-growth native
witness. This is a necessary rate condition for that endpoint estimate,
not a bound on either factor individually.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The quantified actual-gradient endpoint controls the particular
constituent derivative selected by the terminal curl-gradient pair. -/
theorem positiveGrowth_nativeGradient_forces_endpointRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {g E : ℝ → ℝ}
    {B : ℝ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hEndpoint : ActualVelocityGradientLogBoundFrom u a T g E B) :
    ∀ n : ℕ,
      (n : ℝ) + 1 <
        B * (1 + |g (τ n)|) *
          (1 + Real.log (E (τ n))) := by
  intro n
  have hAt := hData.1 n
  have hSelected :
      (n : ℝ) <
        h3TerminalOrientedValue sGradient
          (h3TerminalGradientFieldForPair u p (τ n) (y n)) := by
    have hn := hAt.2.2.2.2
    rw [logValue_h3TerminalNativeGradientForPair] at hn
    exact hn
  have hAbs :
      h3TerminalOrientedValue sGradient
          (h3TerminalGradientFieldForPair u p (τ n) (y n)) ≤
        |h3TerminalGradientFieldForPair u p (τ n) (y n)| :=
    h3TerminalOrientedValue_le_abs sGradient _
  have hBound :=
    hEndpoint (τ n) hAt.1
      (h3TerminalGradientDerivativeAxisForPair p)
      (h3TerminalGradientComponentAxisForPair p)
      (y n)
  change 1 + |h3TerminalGradientFieldForPair u p (τ n) (y n)| ≤
    B * (1 + |g (τ n)|) *
      (1 + Real.log (E (τ n))) at hBound
  linarith

/-- The complete endpoint factor consequently diverges on the
quantitative positive-growth sequence. -/
theorem positiveGrowth_endpointRate_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {g E : ℝ → ℝ}
    {B : ℝ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hEndpoint : ActualVelocityGradientLogBoundFrom u a T g E B) :
    Tendsto
      (fun n : ℕ =>
        B * (1 + |g (τ n)|) *
          (1 + Real.log (E (τ n))))
      atTop atTop := by
  have hIndexed := positiveGrowth_nativeGradient_forces_endpointRate
    hData hEndpoint
  refine tendsto_atTop.2 ?_
  intro M
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact le_of_lt (lt_trans (by linarith : M < (n : ℝ) + 1) (hIndexed n))

/-- In the gradient-dominant relative-escape branch, the actual-gradient
endpoint factor inherits every original-index lower bound from the
selected gradient log. This conclusion remains conditional on the
endpoint estimate and the relative-escape branch. -/
theorem positiveGrowth_gradientRatioEscape_forces_endpointOriginalRate
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
    (hEndpoint : ActualVelocityGradientLogBoundFrom u a T g E B)
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
        B * (1 + |g (τ (k n))|) *
          (1 + Real.log (E (τ (k n)))) := by
  have hGrowth :=
    positiveGrowth_gradientRatioEscape_nativeScale_originalIndex
      hData hCancellation hkTop hRatio M hM
  filter_upwards [hGrowth] with n hn
  have hAt := hData.1 (k n)
  have hBound :=
    hEndpoint (τ (k n)) hAt.1
      (h3TerminalGradientDerivativeAxisForPair p)
      (h3TerminalGradientComponentAxisForPair p)
      (y (k n))
  change 1 + |h3TerminalGradientFieldForPair
      u p (τ (k n)) (y (k n))| ≤
    B * (1 + |g (τ (k n))|) *
      (1 + Real.log (E (τ (k n)))) at hBound
  have hSelectedLeAbs :
      h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) ≤
        |h3TerminalGradientFieldForPair
          u p (τ (k n)) (y (k n))| := by
    unfold h3TerminalOrientedSelectedGradientLogForPair
    rw [logValue_h3TerminalNativeGradientForPair]
    exact h3TerminalOrientedValue_le_abs sGradient _
  linarith

end

end Euclidean
end Bridge
end PrimeTensor
