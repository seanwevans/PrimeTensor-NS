import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointLogFactorSynchronization

/-!
# Joint rate of the canonical BKM endpoint factors

Relative escape forces the canonical BKM endpoint product divided by the
original selected index to diverge. Both nonconstant factors are
eventually nonnegative. Consequently the square of their maximum,
normalized by that index, also diverges. This is a joint rate condition:
it does not assign the rate to one fixed factor.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem endpoint_factor_maxSquare_normalized_atTop
    (k : ℕ → ℕ)
    (B : ℝ)
    (A L : ℕ → ℝ)
    (hB : 0 ≤ B)
    (hA : ∀ n : ℕ, 0 ≤ A n)
    (hL : ∀ᶠ n : ℕ in atTop, 0 ≤ L n)
    (hProduct :
      Tendsto
        (fun n : ℕ => B * A n * L n / ((k n : ℝ) + 1))
        atTop atTop) :
    Tendsto
      (fun n : ℕ => (max (A n) (L n)) ^ 2 / ((k n : ℝ) + 1))
      atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro C
  let D : ℝ := B + 1
  have hDPos : 0 < D := by dsimp [D]; linarith
  have hCLarge : C ≤ max C 0 + 1 := by
    have hCLe := le_max_left C 0
    linarith
  have hLarge : ∀ᶠ n : ℕ in atTop,
      D * (max C 0 + 1) ≤
        B * A n * L n / ((k n : ℝ) + 1) :=
    hProduct.eventually (eventually_ge_atTop (D * (max C 0 + 1)))
  filter_upwards [hL, hLarge] with n hLNonneg hnLarge
  let H : ℝ := max (A n) (L n)
  have hAle : A n ≤ H := le_max_left _ _
  have hLle : L n ≤ H := le_max_right _ _
  have hHNonneg : 0 ≤ H := (hA n).trans hAle
  have hMulFirst : A n * L n ≤ H * L n :=
    mul_le_mul_of_nonneg_right hAle hLNonneg
  have hMulSecond : H * L n ≤ H * H :=
    mul_le_mul_of_nonneg_left hLle hHNonneg
  have hMul : A n * L n ≤ H ^ 2 := by
    nlinarith [hMulFirst, hMulSecond]
  have hBProd : B * (A n * L n) ≤ B * H ^ 2 :=
    mul_le_mul_of_nonneg_left hMul hB
  have hCoeff : B * H ^ 2 ≤ D * H ^ 2 := by
    apply mul_le_mul_of_nonneg_right (show B ≤ D by dsimp [D]; linarith)
    exact sq_nonneg H
  have hBound : B * A n * L n ≤ D * H ^ 2 := by
    calc
      B * A n * L n = B * (A n * L n) := by ring
      _ ≤ B * H ^ 2 := hBProd
      _ ≤ D * H ^ 2 := hCoeff
  have hDen : 0 < (k n : ℝ) + 1 := by positivity
  have hRatioBound :=
    div_le_div_of_nonneg_right hBound (le_of_lt hDen)
  have hScale : D * C ≤ D * (H ^ 2 / ((k n : ℝ) + 1)) := by
    calc
      D * C ≤ D * (max C 0 + 1) :=
        mul_le_mul_of_nonneg_left hCLarge (le_of_lt hDPos)
      _ ≤ B * A n * L n / ((k n : ℝ) + 1) := hnLarge
      _ ≤ D * H ^ 2 / ((k n : ℝ) + 1) := hRatioBound
      _ = D * (H ^ 2 / ((k n : ℝ) + 1)) := by ring
  change C ≤ H ^ 2 / ((k n : ℝ) + 1)
  by_contra hNot
  have hStrict : H ^ 2 / ((k n : ℝ) + 1) < C :=
    lt_of_not_ge hNot
  have hPositive :
      0 < D * (C - H ^ 2 / ((k n : ℝ) + 1)) :=
    mul_pos hDPos (sub_pos.mpr hStrict)
  nlinarith

/-- Gradient-dominant relative escape forces a super-root joint rate
of the vorticity and logarithmic H³ energy factors. -/
theorem positiveGrowth_gradientRatioEscape_canonicalEndpoint_factorMaxRate
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
              u p sGradient (τ (k n)) (y (k n))) :
    Tendsto
      (fun n : ℕ =>
        (max (1 + |g (τ (k n))|)
          (1 + Real.log (velocityH3EnergyAt u (τ (k n))))) ^ 2 /
            ((k n : ℝ) + 1))
      atTop atTop := by
  have hB :
      0 ≤ h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u b)) :=
    h3BKMCanonicalSelectedLogGradientConstant_nonneg
      (Real.sqrt_nonneg _)
  have hLog :=
    (positiveGrowth_relativeWitness_logEnergyFactor_atTop hData hkTop).eventually
      (eventually_ge_atTop 0)
  have hProduct :=
    positiveGrowth_gradientRatioEscape_canonicalEndpoint_normalized_atTop
      hH3 hClass hb hg hData hCancellation hkTop hRatio
  exact endpoint_factor_maxSquare_normalized_atTop k
    (h3BKMCanonicalSelectedLogGradientConstant
      (Real.sqrt (velocityH3Energy0At u b)))
    (fun n => 1 + |g (τ (k n))|)
    (fun n => 1 + Real.log (velocityH3EnergyAt u (τ (k n))))
    hB (fun n => by positivity) hLog hProduct

/-- Curl-dominant relative escape imposes the same joint factor rate. -/
theorem positiveGrowth_curlRatioEscape_canonicalEndpoint_factorMaxRate
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
              u p sGradient (τ (k n)) (y (k n))) :
    Tendsto
      (fun n : ℕ =>
        (max (1 + |g (τ (k n))|)
          (1 + Real.log (velocityH3EnergyAt u (τ (k n))))) ^ 2 /
            ((k n : ℝ) + 1))
      atTop atTop := by
  have hB :
      0 ≤ h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u b)) :=
    h3BKMCanonicalSelectedLogGradientConstant_nonneg
      (Real.sqrt_nonneg _)
  have hLog :=
    (positiveGrowth_relativeWitness_logEnergyFactor_atTop hData hkTop).eventually
      (eventually_ge_atTop 0)
  have hProduct :=
    positiveGrowth_curlRatioEscape_canonicalEndpoint_normalized_atTop
      hH3 hClass hb hg hData hkTop hRatio
  exact endpoint_factor_maxSquare_normalized_atTop k
    (h3BKMCanonicalSelectedLogGradientConstant
      (Real.sqrt (velocityH3Energy0At u b)))
    (fun n => 1 + |g (τ (k n))|)
    (fun n => 1 + Real.log (velocityH3EnergyAt u (τ (k n))))
    hB (fun n => by positivity) hLog hProduct

end

end Euclidean
end Bridge
end PrimeTensor
