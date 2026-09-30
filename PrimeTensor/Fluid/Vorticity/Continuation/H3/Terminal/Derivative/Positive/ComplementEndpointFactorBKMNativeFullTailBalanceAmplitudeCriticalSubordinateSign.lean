import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCriticalThreeScaleSubordinateFrontier

/-!
# Critical half-share subordinate sign extraction

At the critical share `theta = 1/2`, the subordinate signed balance channel is
lower order relative to twice full H³ dissipation, but its sign is not fixed by
the asymptotic share geometry.

A cofinal subsequence can nevertheless freeze one of the three exhaustive sign
possibilities:

* `S < 0`: subleading cancellation;
* `S = 0`: exact single-channel balance;
* `S > 0`: subleading cooperative balance.

The extraction preserves the same critical share cluster and the complete raw,
physical-clock, and energy-normalized subordinate frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A critical subordinate frontier with one fixed pointwise sign along the
selected terminal sequence. -/
def H3TerminalBalanceCriticalSubordinateSignResolvedAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong u T τ
    ∧
  (
    (∀ n : ℕ,
      h3TerminalBalanceSubordinateChannelAt u (τ n) < 0)
      ∨
    (∀ n : ℕ,
      h3TerminalBalanceSubordinateChannelAt u (τ n) = 0)
      ∨
    (∀ n : ℕ,
      0 < h3TerminalBalanceSubordinateChannelAt u (τ n))
  )

private theorem criticalSubordinateSign_reindex
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    {k : ℕ → ℕ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2)
    (hKMono : StrictMono k) :
    H3TerminalBalanceShareClusterAlong
        u T (fun n : ℕ => τ (k n)) theta
      ∧
    H3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong
        u T (fun n : ℕ => τ (k n)) := by
  have hKTop : Tendsto k atTop atTop :=
    hKMono.tendsto_atTop

  have hTauSub :
      Tendsto (fun n : ℕ => τ (k n)) atTop (𝓝 T) :=
    hCluster.1.1.comp hKTop

  have hAtSub :
      ∀ n : ℕ,
        τ (k n) ∈ Set.Ioo a T :=
    fun n => hAt (k n)

  have hCascadeSub :
      H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong
        u T (fun n : ℕ => τ (k n)) :=
    h3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hTauSub
      (fun n => (hAtSub n).2)

  have hClusterSub :
      H3TerminalBalanceShareClusterAlong
        u T (fun n : ℕ => τ (k n)) theta :=
    ⟨
      hCascadeSub,
      hCluster.2.1.comp hKTop,
      hCluster.2.2.comp hKTop
    ⟩

  have hFrontierSub :
      H3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong
        u T (fun n : ℕ => τ (k n)) :=
    h3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong_of_shareCluster_eq_half
      hH3
      hClass
      hAtSub
      hClusterSub
      hTheta

  exact ⟨hClusterSub, hFrontierSub⟩

/-- At critical half-share, a cofinal subsequence freezes the sign of the
subordinate channel while preserving the full critical share cluster and all
three subordinate frontier factorizations. -/
theorem exists_fixed_balanceCriticalSubordinateSign_subsequence_of_shareCluster_eq_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      H3TerminalBalanceShareClusterAlong
        u T (fun n : ℕ => τ (k n)) theta
        ∧
      H3TerminalBalanceCriticalSubordinateSignResolvedAlong
        u T (fun n : ℕ => τ (k n)) := by
  classical

  let S : ℕ → ℝ :=
    fun n => h3TerminalBalanceSubordinateChannelAt u (τ n)

  by_cases hNegativeFrequently :
      ∃ᶠ n : ℕ in atTop,
        S n < 0

  · obtain ⟨k, hKMono, hKNegative⟩ :=
      extraction_of_frequently_atTop hNegativeFrequently

    obtain ⟨hClusterSub, hFrontierSub⟩ :=
      criticalSubordinateSign_reindex
        hH3 hNoExtension hClass hAt hCluster hTheta hKMono

    refine
      ⟨
        k,
        hKMono,
        hClusterSub,
        hFrontierSub,
        Or.inl ?_
      ⟩

    intro n
    simpa only [S] using hKNegative n

  · have hEventuallyNotNegative :
        ∀ᶠ n : ℕ in atTop,
          ¬ S n < 0 :=
      (not_frequently).1 hNegativeFrequently

    have hEventuallyNonnegative :
        ∀ᶠ n : ℕ in atTop,
          0 ≤ S n := by
      filter_upwards [hEventuallyNotNegative] with n hn
      exact le_of_not_gt hn

    by_cases hPositiveFrequently :
        ∃ᶠ n : ℕ in atTop,
          0 < S n

    · obtain ⟨k, hKMono, hKPositive⟩ :=
        extraction_of_frequently_atTop hPositiveFrequently

      obtain ⟨hClusterSub, hFrontierSub⟩ :=
        criticalSubordinateSign_reindex
          hH3 hNoExtension hClass hAt hCluster hTheta hKMono

      refine
        ⟨
          k,
          hKMono,
          hClusterSub,
          hFrontierSub,
          Or.inr (Or.inr ?_)
        ⟩

      intro n
      simpa only [S] using hKPositive n

    · have hEventuallyNotPositive :
          ∀ᶠ n : ℕ in atTop,
            ¬ 0 < S n :=
        (not_frequently).1 hPositiveFrequently

      have hEventuallyZero :
          ∀ᶠ n : ℕ in atTop,
            S n = 0 := by
        filter_upwards
          [hEventuallyNonnegative, hEventuallyNotPositive]
          with n hNonnegative hNotPositive
        exact le_antisymm (le_of_not_gt hNotPositive) hNonnegative

      obtain ⟨k, hKMono, hKZero⟩ :=
        extraction_of_eventually_atTop hEventuallyZero

      obtain ⟨hClusterSub, hFrontierSub⟩ :=
        criticalSubordinateSign_reindex
          hH3 hNoExtension hClass hAt hCluster hTheta hKMono

      refine
        ⟨
          k,
          hKMono,
          hClusterSub,
          hFrontierSub,
          Or.inr (Or.inl ?_)
        ⟩

      intro n
      simpa only [S] using hKZero n

end

end Euclidean
end Bridge
end PrimeTensor
