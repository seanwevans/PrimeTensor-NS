import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Finite.Reciprocal.Cluster

/-!
# Finite endpoint relative-rate dichotomy

Under the physical ceilings, a finite normalized-gap cluster separates into
ratio matching when the cluster value is zero and finite positive relative
separation when it is nonzero. Both cases preserve one strictly increasing
quantitative native subsequence and both reciprocal limits.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The two finite relative-rate outcomes, without a divergent-ratio
branch. The same native sequence carries each set of limits. -/
def H3TerminalEndpointFiniteRateDichotomyLift
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3)
    (gap ratio reciprocal : ℕ → ℝ) : Prop :=
  (∃ k : ℕ → ℕ,
    StrictMono k ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient
          (fun n => τ (k n)) (fun n => y (k n)) ∧
      Tendsto (fun n : ℕ => gap (k n)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n : ℕ => ratio (k n)) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun n : ℕ => reciprocal (k n)) atTop (𝓝 (1 : ℝ))) ∨
  (∃ c : ℝ, 0 < c ∧
    ∃ k : ℕ → ℕ,
      StrictMono k ∧
        H3TerminalPositiveGrowthQuantitativeNativeData
          u a T p sCurl sGradient
            (fun n => τ (k n)) (fun n => y (k n)) ∧
        Tendsto (fun n : ℕ => gap (k n)) atTop (𝓝 c) ∧
        Tendsto (fun n : ℕ => ratio (k n)) atTop (𝓝 (1 + c)) ∧
        Tendsto (fun n : ℕ => reciprocal (k n))
          atTop (𝓝 ((1 + c)⁻¹)))

/-- A nonnegative finite cluster must be either matching or positively
separated; the reciprocal limits are retained in either case. -/
theorem finiteRateDichotomyLift_of_nonnegative_cluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {gap ratio reciprocal : ℕ → ℝ}
    {c : ℝ}
    {k : ℕ → ℕ}
    (hc : 0 ≤ c)
    (hkMono : StrictMono k)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient
          (fun n => τ (k n)) (fun n => y (k n)))
    (hGap : Tendsto (fun n : ℕ => gap (k n)) atTop (𝓝 c))
    (hRatio : Tendsto (fun n : ℕ => ratio (k n)) atTop (𝓝 (1 + c)))
    (hReciprocal : Tendsto (fun n : ℕ => reciprocal (k n))
      atTop (𝓝 ((1 + c)⁻¹))) :
    H3TerminalEndpointFiniteRateDichotomyLift
      u a T p sCurl sGradient τ y gap ratio reciprocal := by
  unfold H3TerminalEndpointFiniteRateDichotomyLift
  rcases eq_or_lt_of_le hc with hZero | hPositive
  · subst c
    refine Or.inl ⟨k, hkMono, hData, ?_, ?_, ?_⟩
    · simpa using hGap
    · simpa using hRatio
    · simpa using hReciprocal
  · exact Or.inr ⟨c, hPositive, k, hkMono, hData,
      hGap, hRatio, hReciprocal⟩

/-- Orient the finite alternatives using the complementary-gradient
dominance direction of a relative-gap witness. -/
def H3TerminalEndpointFiniteRateDichotomyAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  (let A : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ n) (y n);
   let B : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ n) (y n);
   (sComplement = sGradient ∧
      H3TerminalEndpointFiniteRateDichotomyLift
        u a T p sCurl sGradient τ y
          (fun n => (A n - B n) / B n)
          (fun n => A n / B n)
          (fun n => B n / A n)) ∨
   (sComplement ≠ sGradient ∧
      H3TerminalEndpointFiniteRateDichotomyLift
        u a T p sCurl sGradient τ y
          (fun n => (B n - A n) / A n)
          (fun n => B n / A n)
          (fun n => A n / B n)))

/-- Conditional on nonextension and the three endpoint ceilings, any
relative-gap native witness has either ratio matching or a finite positive
relative-rate cluster. -/
theorem positiveGrowth_endpoint_finiteRateDichotomy_of_exponentialCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
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
        u b T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y)
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B)
    (hCeiling : H3TerminalEndpointExponentialPhysicalCeilingData u τ) :
    H3TerminalEndpointFiniteRateDichotomyAt
      u b T p sCurl sGradient sComplement τ y := by
  obtain ⟨c, hc, _, k, hkMono, hData', hBranch⟩ :=
    positiveGrowth_endpoint_finiteReciprocalCluster_of_exponentialCeiling
      hH3 hNoExtension hClass hb hg hData hCancellation hRelative
      C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
  unfold H3TerminalEndpointFiniteRateDichotomyAt
  dsimp only
  rcases hBranch with ⟨hSame, hGap, hRatio, hReciprocal⟩ |
    ⟨hOpp, hGap, hRatio, hReciprocal⟩
  · exact Or.inl ⟨hSame,
      finiteRateDichotomyLift_of_nonnegative_cluster
        hc hkMono hData' hGap hRatio hReciprocal⟩
  · exact Or.inr ⟨hOpp,
      finiteRateDichotomyLift_of_nonnegative_cluster
        hc hkMono hData' hGap hRatio hReciprocal⟩

end

end Euclidean
end Bridge
end PrimeTensor
