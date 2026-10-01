import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Alternative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Tail.Cascade

/-!
# Persistent factor branch after cofinal extraction

The pointwise factor alternative need not choose the same factor at
every index. Apply the existing bounded-or-cofinal tail lemma to the
normalized vorticity-factor square. If that factor is unbounded on
every tail, it diverges on a cofinal extraction. If it is eventually
bounded, the squared maximum rate forces the logarithmic energy-factor
square to diverge along the entire relative-escape subsequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem maxSquareRate_factorBranch
    (k : ℕ → ℕ)
    (A L : ℕ → ℝ)
    (hMax :
      Tendsto
        (fun n : ℕ => (max (A n) (L n)) ^ 2 / ((k n : ℝ) + 1))
        atTop atTop) :
    (∃ j : ℕ → ℕ,
      Tendsto j atTop atTop ∧
        Tendsto
          (fun n : ℕ => (A (j n)) ^ 2 / ((k (j n) : ℝ) + 1))
          atTop atTop) ∨
      Tendsto
        (fun n : ℕ => (L n) ^ 2 / ((k n : ℝ) + 1))
        atTop atTop := by
  classical
  let f : ℕ → ℝ := fun n => (A n) ^ 2 / ((k n : ℝ) + 1)
  have hIdentity :
      ∀ᶠ n : ℕ in atTop, (1 + f n : ℝ) = 1 + f n :=
    Eventually.of_forall (fun _ => rfl)
  have hTail :=
    relativeTailAlternative_of_eventually_ratio_identity
      f (fun n => 1 + f n) hIdentity
  unfold H3TerminalRelativeTailAlternative at hTail
  rcases hTail with ⟨C, hBound⟩ | ⟨j, _, hjTop, hfTop, _⟩
  · right
    have hFBound : ∀ᶠ n : ℕ in atTop, f n ≤ C :=
      hBound.mono (fun n hn => hn.1)
    refine tendsto_atTop.2 ?_
    intro M
    let D : ℝ := max C M + 1
    have hCGt : C < D := by
      dsimp [D]
      have hCLe := le_max_left C M
      linarith
    have hMLe : M ≤ D := by
      dsimp [D]
      have hMLeMax := le_max_right C M
      linarith
    have hMaxLarge : ∀ᶠ n : ℕ in atTop,
        D < (max (A n) (L n)) ^ 2 / ((k n : ℝ) + 1) :=
      hMax.eventually (eventually_gt_atTop D)
    filter_upwards [hFBound, hMaxLarge] with n hnBound hnMax
    rcases le_total (A n) (L n) with hAL | hLA
    · have hRate : D < (L n) ^ 2 / ((k n : ℝ) + 1) := by
        simpa only [max_eq_right hAL] using hnMax
      exact hMLe.trans (le_of_lt hRate)
    · have hRate : D < f n := by
        simpa only [max_eq_left hLA, f] using hnMax
      exact False.elim ((not_lt_of_ge hnBound) (lt_trans hCGt hRate))
  · left
    exact ⟨j, hjTop, by simpa only [f] using hfTop⟩

/-- Gradient-dominant relative escape has a cofinal vorticity-factor
rate branch or a full log-energy-factor rate branch. -/
theorem positiveGrowth_gradientRatioEscape_endpoint_factorBranch
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
    (∃ j : ℕ → ℕ,
      Tendsto j atTop atTop ∧
        Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (j n)))|) ^ 2 /
              ((k (j n) : ℝ) + 1))
          atTop atTop) ∨
      Tendsto
        (fun n : ℕ =>
          (1 + Real.log (velocityH3EnergyAt u (τ (k n)))) ^ 2 /
            ((k n : ℝ) + 1))
        atTop atTop := by
  exact maxSquareRate_factorBranch k
    (fun n => 1 + |g (τ (k n))|)
    (fun n => 1 + Real.log (velocityH3EnergyAt u (τ (k n))))
    (positiveGrowth_gradientRatioEscape_canonicalEndpoint_factorMaxRate
      hH3 hClass hb hg hData hCancellation hkTop hRatio)

/-- Curl-dominant relative escape has the same cofinal vorticity or
full log-energy factor-rate alternative. -/
theorem positiveGrowth_curlRatioEscape_endpoint_factorBranch
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
    (∃ j : ℕ → ℕ,
      Tendsto j atTop atTop ∧
        Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (j n)))|) ^ 2 /
              ((k (j n) : ℝ) + 1))
          atTop atTop) ∨
      Tendsto
        (fun n : ℕ =>
          (1 + Real.log (velocityH3EnergyAt u (τ (k n)))) ^ 2 /
            ((k n : ℝ) + 1))
        atTop atTop := by
  exact maxSquareRate_factorBranch k
    (fun n => 1 + |g (τ (k n))|)
    (fun n => 1 + Real.log (velocityH3EnergyAt u (τ (k n))))
    (positiveGrowth_curlRatioEscape_canonicalEndpoint_factorMaxRate
      hH3 hClass hb hg hData hkTop hRatio)

end

end Euclidean
end Bridge
end PrimeTensor
