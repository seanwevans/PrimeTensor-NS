import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Share.Regime.Cascade

/-!
# Canonical nonextension witness for the balance-share clock regimes

The preceding development first extracts a compact asymptotic dissipation-share
parameter `theta`, and then classifies every such share cluster into three
quantitative regimes around the threshold `1/2`.

This file composes those two stages.  Under hypothetical nonextension, one
explicit terminal sequence carries

* the canonical balance-amplitude polynomial rates at every selected time,
* the full balance-amplitude and intrinsic H³ cascade,
* a share parameter `theta ∈ [0,1]`, and
* exactly one of the quantitative cancellation, critical, or cooperative
  clock regimes.

The original dissipation-scale versus imbalance-scale extraction is no longer
needed by downstream users of this package.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A single explicit terminal witness carrying the asymptotic share parameter,
canonical amplitude rates, full intrinsic cascade, and its quantitative clock
regime. -/
def H3TerminalBalanceShareRegimeWitness
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b : ℝ) : Prop :=
  ∃ theta : ℝ,
    theta ∈ Set.Icc (0 : ℝ) 1
      ∧
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ,
        τ n ∈ Set.Ioo b T
          ∧
        H3TerminalBalanceAmplitudePolynomialRatesAt u T b (τ n))
        ∧
      H3TerminalBalanceShareClusterAlong u T τ theta
        ∧
      (
        (
          theta < (1 : ℝ) / 2
            ∧
          H3TerminalBalanceCancellationClockCascadeAlong u T τ
        )
          ∨
        (
          theta = (1 : ℝ) / 2
            ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalBalanceSubordinateChannelAt u (τ n) /
                h3TerminalBalanceAmplitudeAt u (τ n))
            atTop (𝓝 (0 : ℝ))
        )
          ∨
        (
          (1 : ℝ) / 2 < theta
            ∧
          H3TerminalBalanceCooperativeClockCascadeAlong u T τ
        )
      )

/-- Hypothetical nonextension produces one explicit balance-share regime witness
on every strict terminal subtail. -/
theorem exists_terminal_balanceShareRegimeWitness_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    H3TerminalBalanceShareRegimeWitness u T b := by
  rcases
    exists_fixed_balanceAmplitudeShare_cluster_of_noH3PathExtension
      hH3 hNoExtension hClass hb
    with hDissipation | hImbalance

  · rcases hDissipation with
      ⟨theta, hTheta, τ, hData, hCluster⟩

    have hTheta01 :
        theta ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [hTheta.1], hTheta.2⟩

    have hAt :
        ∀ n : ℕ,
          τ n ∈ Set.Ioo a T := by
      intro n
      exact
        ⟨
          lt_trans hb.1 (hData n).1.1,
          (hData n).1.2
        ⟩

    have hRegime :=
      h3TerminalBalanceShareCluster_clockCascade_trichotomy
        hH3 hClass hAt hCluster

    refine
      ⟨
        theta,
        hTheta01,
        τ,
        ?_,
        hCluster,
        hRegime
      ⟩

    intro n
    exact
      ⟨
        (hData n).1,
        (hData n).2.1
      ⟩

  · rcases hImbalance with
      ⟨theta, hTheta, τ, hData, hCluster, _hImbalanceCascade⟩

    have hTheta01 :
        theta ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨hTheta.1, by linarith [hTheta.2]⟩

    have hAt :
        ∀ n : ℕ,
          τ n ∈ Set.Ioo a T := by
      intro n
      exact
        ⟨
          lt_trans hb.1 (hData n).1.1,
          (hData n).1.2
        ⟩

    have hRegime :=
      h3TerminalBalanceShareCluster_clockCascade_trichotomy
        hH3 hClass hAt hCluster

    refine
      ⟨
        theta,
        hTheta01,
        τ,
        ?_,
        hCluster,
        hRegime
      ⟩

    intro n
    exact
      ⟨
        (hData n).1,
        (hData n).2.1
      ⟩

/-- Neutral formulation: either the H³ path continues smoothly, or one explicit
terminal sequence realizes one of the three quantitative balance-share clock
regimes. -/
theorem smoothContinuationExtension_or_terminal_balanceShareRegimeWitness
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    H3TerminalBalanceShareRegimeWitness u T b := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_terminal_balanceShareRegimeWitness_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor specialization of the unified quantitative
balance-share regime witness. -/
theorem exists_terminal_balanceShareRegimeWitness_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalBalanceShareRegimeWitness
      u T (h3BKMKineticTailMidpoint a T) := by
  exact
    exists_terminal_balanceShareRegimeWitness_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
