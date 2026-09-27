import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRatioCascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientCancellationSubsequence

/-!
# Triple native escape on a positive-growth subsequence

In the unbounded cancellation branch, the complementary logarithm is large
arbitrarily far out along one fixed orientation.  The quantitative curl and
selected-gradient bounds already hold at every original index.  Hence a single
index map `k` with `n ≤ k n` and complementary magnitude above `n` preserves
both earlier bounds without another diagonal extraction.

The composed time and point sequence retains the indexed positive H³ energy
derivative bound and every scalar and frequency limit of the original cascade.
All three native quantities escape one-sidedly on that same subsequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Quantitative positive growth with curl, selected gradient, and
complementary gradient escaping on one time and point sequence. -/
def H3TerminalPositiveGrowthTripleNativeCascade
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation) : Prop :=
  ∃ τ : ℕ → ℝ,
    ∃ y : ℕ → Point3,
      H3TerminalPositiveGrowthQuantitativeNativeData
          u a T p sCurl sGradient τ y
        ∧
      H3TerminalComplementCancellationRegime p sCurl sGradient
        ∧
      (∀ n : ℕ,
        (n : ℝ) <
          h3TerminalOrientedValue sComplement
            (PrimeTensor.Bridge.MulReal.logValue
              (h3TerminalNativeComplementGradientForPair
                u p (τ n) (y n))))
        ∧
      H3TerminalNativeLogDirectionalEscape
        (fun n : ℕ =>
          h3TerminalNativeComplementGradientForPair
            u p (τ n) (y n))
        sComplement

/-- A tail-cofinally unbounded complementary orientation admits a further
subsequence that retains all quantitative positive-growth data and makes the
third native logarithm exceed `n`. -/
theorem positiveGrowth_tripleNativeCascade_of_complementCofinal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime
        p sCurl sGradient)
    (hCofinal :
      H3TerminalScalarSeqOrientedTailCofinallyUnbounded
        (fun n : ℕ =>
          PrimeTensor.Bridge.MulReal.logValue
            (h3TerminalNativeComplementGradientForPair
              u p (τ n) (y n)))
        sComplement) :
    H3TerminalPositiveGrowthTripleNativeCascade
      u a T p sCurl sGradient sComplement := by
  classical
  obtain ⟨hAt, hTau, hEnergy, hDiss, hTransport, hFrequency,
      hCurlEscape, hGradientEscape, _hDirectional⟩ := hData

  have hChoice :
      ∀ n : ℕ,
        ∃ m : ℕ,
          n ≤ m
            ∧
          (n : ℝ) <
            h3TerminalOrientedValue sComplement
              (PrimeTensor.Bridge.MulReal.logValue
                (h3TerminalNativeComplementGradientForPair
                  u p (τ m) (y m))) := by
    intro n
    exact hCofinal n (n : ℝ)
  choose k hk using hChoice

  have hkTop : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hk n).1

  let τ' : ℕ → ℝ := fun n => τ (k n)
  let y' : ℕ → Point3 := fun n => y (k n)

  have hAt' :
      ∀ n : ℕ,
        τ' n ∈ Set.Ioo a T
          ∧
        τ' n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T
          ∧
        (n : ℝ) < deriv (velocityH3EnergyAt u) (τ' n)
          ∧
        (n : ℝ) <
          h3TerminalOrientedValue sCurl
            (PrimeTensor.Bridge.MulReal.logValue
              (h3TerminalNativeCurlForPair u p (τ' n) (y' n)))
          ∧
        (n : ℝ) <
          h3TerminalOrientedValue sGradient
            (PrimeTensor.Bridge.MulReal.logValue
              (h3TerminalNativeGradientForPair u p (τ' n) (y' n))) := by
    intro n
    have hOrig := hAt (k n)
    have hIndex : (n : ℝ) ≤ (k n : ℝ) := by
      exact_mod_cast (hk n).1
    have hDenPos : 0 < (n : ℝ) + 1 := by positivity
    have hDenLe :
        (n : ℝ) + 1 ≤ (k n : ℝ) + 1 := by linarith
    have hInv :
        (1 : ℝ) / ((k n : ℝ) + 1)
          ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hDenPos hDenLe
    have hNear :
        τ' n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T := by
      constructor
      · dsimp only [τ']
        linarith [hOrig.2.1.1, hInv]
      · dsimp only [τ']
        exact hOrig.2.1.2
    exact ⟨hOrig.1, hNear,
      lt_of_le_of_lt hIndex hOrig.2.2.1,
      lt_of_le_of_lt hIndex hOrig.2.2.2.1,
      lt_of_le_of_lt hIndex hOrig.2.2.2.2⟩

  have hTau' : Tendsto τ' atTop (𝓝 T) :=
    hTau.comp hkTop
  have hEnergy' :
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ' n))
        atTop atTop :=
    hEnergy.comp hkTop
  have hDiss' :
      Tendsto
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ' n) /
            velocityH3EnergyAt u (τ' n))
        atTop atTop :=
    hDiss.comp hkTop
  have hTransport' :
      Tendsto
        (fun n : ℕ =>
          (-velocityH3TransportDerivativeAt u (τ' n)) /
            velocityH3EnergyAt u (τ' n))
        atTop atTop :=
    hTransport.comp hkTop
  have hFrequency' :
      Tendsto
        (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ' n))
        atTop atTop :=
    hFrequency.comp hkTop

  have hCurlEscape' :
      H3TerminalNativeLogDirectionalEscape
        (fun n : ℕ =>
          h3TerminalNativeCurlForPair u p (τ' n) (y' n))
        sCurl :=
    nativeLogDirectionalEscape_comp_atTop hCurlEscape hkTop
  have hGradientEscape' :
      H3TerminalNativeLogDirectionalEscape
        (fun n : ℕ =>
          h3TerminalNativeGradientForPair u p (τ' n) (y' n))
        sGradient :=
    nativeLogDirectionalEscape_comp_atTop hGradientEscape hkTop

  have hComplementBound :
      ∀ n : ℕ,
        (n : ℝ) <
          h3TerminalOrientedValue sComplement
            (PrimeTensor.Bridge.MulReal.logValue
              (h3TerminalNativeComplementGradientForPair
                u p (τ' n) (y' n))) := by
    intro n
    exact (hk n).2

  have hComplementTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedValue sComplement
            (PrimeTensor.Bridge.MulReal.logValue
              (h3TerminalNativeComplementGradientForPair
                u p (τ' n) (y' n))))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop N] with n hn
    have hCast : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact le_of_lt (lt_trans (lt_of_lt_of_le hN hCast)
      (hComplementBound n))

  have hComplementEscape :
      H3TerminalNativeLogDirectionalEscape
        (fun n : ℕ =>
          h3TerminalNativeComplementGradientForPair
            u p (τ' n) (y' n))
        sComplement := by
    exact nativeLogDirectionalEscape_of_oriented_log_bridge
      (Ω := fun n : ℕ =>
        h3TerminalNativeComplementGradientForPair
          u p (τ' n) (y' n))
      (H := fun n : ℕ =>
        PrimeTensor.Bridge.MulReal.logValue
          (h3TerminalNativeComplementGradientForPair
            u p (τ' n) (y' n)))
      (s := sComplement)
      (fun n => rfl)
      hComplementTop

  have hDirectional' :
      H3TerminalNativeCurlGradientDoubleDirectionalEscape
        u a T p sCurl sGradient := by
    refine ⟨τ', y', ?_, hTau', hCurlEscape', hGradientEscape'⟩
    intro n
    exact ⟨(hAt' n).1, (hAt' n).2.1,
      (hAt' n).2.2.2.1, (hAt' n).2.2.2.2⟩

  have hData' :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ' y' := by
    exact ⟨hAt', hTau', hEnergy', hDiss', hTransport', hFrequency',
      hCurlEscape', hGradientEscape', hDirectional'⟩
  exact ⟨τ', y', hData', hCancellation,
    hComplementBound, hComplementEscape⟩

end

end Euclidean
end Bridge
end PrimeTensor
