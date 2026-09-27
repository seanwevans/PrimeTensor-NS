import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeTailCascade

/-!
# Cofinal reindexing of the positive-growth relative escape branch

An index map satisfying `n ≤ k n` preserves every indexed lower bound in
the quantitative native cascade. It also tends to `+∞`, so all scalar and
native escape limits pass to the composed time and point sequences. This
lemma upgrades the relative-gap cofinal escape branch to a full synchronized
positive-growth witness on its extracted subsequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The complete quantitative native cascade survives any reindexing with
`n ≤ k n`. In particular, the near-terminal window and derivative bounds
retain their original index thresholds. -/
theorem positiveGrowth_quantitativeNativeData_comp_cofinal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    {k : ℕ → ℕ}
    (hk : ∀ n : ℕ, n ≤ k n) :
    H3TerminalPositiveGrowthQuantitativeNativeData
      u a T p sCurl sGradient
        (fun n => τ (k n)) (fun n => y (k n)) := by
  classical
  obtain ⟨hAt, hTau, hEnergy, hDiss, hTransport, hFrequency,
    hCurlEscape, hGradientEscape, _hDirectional⟩ := hData

  have hkTop : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hk n)

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
      exact_mod_cast (hk n)
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

  have hDirectional' :
      H3TerminalNativeCurlGradientDoubleDirectionalEscape
        u a T p sCurl sGradient := by
    refine ⟨τ', y', ?_, hTau', hCurlEscape', hGradientEscape'⟩
    intro n
    exact ⟨(hAt' n).1, (hAt' n).2.1,
      (hAt' n).2.2.2.1, (hAt' n).2.2.2.2⟩

  exact ⟨hAt', hTau', hEnergy', hDiss', hTransport', hFrequency',
    hCurlEscape', hGradientEscape', hDirectional'⟩

/-- The relative tail split strengthened with a complete positive-growth
native cascade on the escaping subsequence. -/
def H3TerminalPositiveGrowthRelativeTailLift
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3)
    (gap ratio : ℕ → ℝ) : Prop :=
  (∃ C : ℝ,
    ∀ᶠ n : ℕ in atTop,
      gap n ≤ C ∧ ratio n ≤ 1 + C)
    ∨
  (∃ k : ℕ → ℕ,
    H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient
          (fun n => τ (k n)) (fun n => y (k n))
      ∧
    (∀ n : ℕ,
      n ≤ k n
        ∧
      (n : ℝ) < gap (k n)
        ∧
      (n : ℝ) + 1 < ratio (k n))
      ∧
    Tendsto k atTop atTop
      ∧
    Tendsto (fun n : ℕ => gap (k n)) atTop atTop
      ∧
    Tendsto (fun n : ℕ => ratio (k n)) atTop atTop)

/-- Insert the inherited positive-growth data in the cofinal escape branch
of an already established relative tail alternative. -/
theorem positiveGrowth_relativeTailLift_of_alternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {gap ratio : ℕ → ℝ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hTail : H3TerminalRelativeTailAlternative gap ratio) :
    H3TerminalPositiveGrowthRelativeTailLift
      u a T p sCurl sGradient τ y gap ratio := by
  rcases hTail with hBound | ⟨k, hk, hkTop, hGapTop, hRatioTop⟩
  · exact Or.inl hBound
  · exact Or.inr ⟨k,
      positiveGrowth_quantitativeNativeData_comp_cofinal hData
        (fun n => (hk n).1),
      hk, hkTop, hGapTop, hRatioTop⟩

/-- A branch-aware relative tail split whose cofinal branch explicitly
retains every quantitative positive-growth conclusion. -/
def H3TerminalPositiveGrowthRelativeTailLiftedAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthRelativeTailAlternativeAt
      u p sGradient sComplement τ y
    ∧
  (let A : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ n) (y n);
   let B : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ n) (y n);
   (sComplement = sGradient
      ∧
      H3TerminalPositiveGrowthRelativeTailLift
        u a T p sCurl sGradient τ y
          (fun n : ℕ => (A n - B n) / B n)
          (fun n : ℕ => A n / B n))
    ∨
    (sComplement ≠ sGradient
      ∧
      H3TerminalPositiveGrowthRelativeTailLift
        u a T p sCurl sGradient τ y
          (fun n : ℕ => (B n - A n) / A n)
          (fun n : ℕ => B n / A n)))

/-- The triple native branch resolves the relative tail alternative while
retaining the full quantitative cascade even in the cofinal escape case. -/
theorem positiveGrowth_relativeTailLifted_of_tripleNativeCascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    (hTriple :
      H3TerminalPositiveGrowthTripleNativeCascade
        u a T p sCurl sGradient sComplement) :
    ∃ τ : ℕ → ℝ,
      ∃ y : ℕ → Point3,
        H3TerminalPositiveGrowthQuantitativeNativeData
            u a T p sCurl sGradient τ y
          ∧
        H3TerminalComplementCancellationRegime
            p sCurl sGradient
          ∧
        H3TerminalPositiveGrowthRelativeTailLiftedAt
            u a T p sCurl sGradient sComplement τ y := by
  classical
  obtain ⟨τ, y, hData, hCancellation, hTail⟩ :=
    positiveGrowth_relativeTailAlternative_of_tripleNativeCascade hTriple
  refine ⟨τ, y, hData, hCancellation, hTail, ?_⟩
  dsimp only
  rcases hTail.2 with ⟨hSame, hAlternative⟩ | ⟨hOpp, hAlternative⟩
  · exact Or.inl ⟨hSame,
      positiveGrowth_relativeTailLift_of_alternative hData hAlternative⟩
  · exact Or.inr ⟨hOpp,
      positiveGrowth_relativeTailLift_of_alternative hData hAlternative⟩

end

end Euclidean
end Bridge
end PrimeTensor
