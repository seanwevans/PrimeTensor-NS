import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCriticalOrientation

/-!
# Fully resolved terminal balance-share regime witness

The unified balance-share witness already classifies every hypothetical
nonextension cluster by the asymptotic dissipation share `theta` relative to
`1/2`.  The cancellation and critical regimes still require a finite channel
choice before their strongest conclusions can be stated on one fixed sequence.

This file performs those final extractions once and packages the result as a
single downstream interface.

* `theta < 1/2`: one cancellation orientation is frozen.  The selected
  opposite-sign channel carries raw, physical-clock, and energy-normalized
  divergence; in the positive-energy-growth orientation the minimal vorticity
  envelope and actual vorticity also diverge on the same times.
* `theta = 1/2`: one dominant balance channel is frozen.  It carries the full
  raw/clock/normalized amplitude cascade while the subordinate channel is
  negligible relative to the amplitude.
* `theta > 1/2`: the cooperative cascade is already branch-free and is retained
  on the original witness sequence.

No additional analytic estimate is introduced here; the proof only composes
previously established terminal extractions and reindexes the polynomial-rate
witness data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Fully resolved cancellation regime on one fixed sequence. -/
def H3TerminalBalanceCancellationResolvedClockCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  (
    (
      (∀ n : ℕ,
        h3TerminalBalanceSubordinateChannelAt u (τ n)
            = - deriv (velocityH3EnergyAt u) (τ n)
          ∧
        h3TerminalBalanceAmplitudeAt u (τ n)
            = - velocityH3TransportDerivativeAt u (τ n))
        ∧
      Tendsto
        (fun n : ℕ => deriv (velocityH3EnergyAt u) (τ n))
        atTop atTop
        ∧
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * deriv (velocityH3EnergyAt u) (τ n))
        atTop atTop
        ∧
      Tendsto
        (fun n : ℕ =>
          deriv (velocityH3EnergyAt u) (τ n) /
            velocityH3EnergyAt u (τ n))
        atTop atTop
        ∧
      Tendsto
        (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
        atTop atTop
        ∧
      ∃ y : ℕ → Point3,
        Tendsto
          (fun n : ℕ => h3ActualVorticityMaxAt u (τ n) (y n))
          atTop atTop
    )
      ∨
    (
      (∀ n : ℕ,
        h3TerminalBalanceSubordinateChannelAt u (τ n)
            = - velocityH3TransportDerivativeAt u (τ n)
          ∧
        h3TerminalBalanceAmplitudeAt u (τ n)
            = - deriv (velocityH3EnergyAt u) (τ n))
        ∧
      Tendsto
        (fun n : ℕ => velocityH3TransportDerivativeAt u (τ n))
        atTop atTop
        ∧
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * velocityH3TransportDerivativeAt u (τ n))
        atTop atTop
        ∧
      Tendsto
        (fun n : ℕ =>
          velocityH3TransportDerivativeAt u (τ n) /
            velocityH3EnergyAt u (τ n))
        atTop atTop
    )
  )

/-- Fully resolved critical half-share regime on one fixed sequence. -/
def H3TerminalBalanceCriticalResolvedClockCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalDecayDominantClockCascadeAlong u T τ
    ∨
  H3TerminalBalanceCriticalTransportDominantClockCascadeAlong u T τ

/-- One explicit terminal sequence carrying the canonical amplitude polynomial
rates, full share/intrinsic cluster, and a fully resolved quantitative regime. -/
def H3TerminalBalanceResolvedRegimeWitness
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
          H3TerminalBalanceCancellationResolvedClockCascadeAlong u T τ
        )
          ∨
        (
          theta = (1 : ℝ) / 2
            ∧
          H3TerminalBalanceCriticalResolvedClockCascadeAlong u T τ
        )
          ∨
        (
          (1 : ℝ) / 2 < theta
            ∧
          H3TerminalBalanceCooperativeClockCascadeAlong u T τ
        )
      )

/-- Hypothetical nonextension produces one fully resolved balance-share regime
witness on every strict terminal subtail. -/
theorem exists_terminal_balanceResolvedRegimeWitness_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    H3TerminalBalanceResolvedRegimeWitness u T b := by
  rcases
    exists_terminal_balanceShareRegimeWitness_of_noH3PathExtension
      hH3 hNoExtension hClass hb
    with ⟨theta, hTheta, τ, hData, hCluster, hRegime⟩

  have hAt :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T := by
    intro n
    exact
      ⟨
        lt_trans hb.1 (hData n).1.1,
        (hData n).1.2
      ⟩

  rcases hRegime with hCancellation | hCritical | hCooperative

  · rcases hCancellation with ⟨hThetaLt, _hCancellationClock⟩

    obtain ⟨k, _hKMono, hClusterSub, hOrientation⟩ :=
      exists_fixed_balanceCancellationOrientation_clockRatesActualVorticitySubsequence_of_shareCluster_lt_half
        hH3 hNoExtension hClass hb hAt hCluster hThetaLt

    refine
      ⟨
        theta,
        hTheta,
        (fun n : ℕ => τ (k n)),
        ?_,
        hClusterSub,
        Or.inl ⟨hThetaLt, hOrientation⟩
      ⟩

    intro n
    exact hData (k n)

  · rcases hCritical with ⟨hThetaEq, _hSubordinateZero⟩

    obtain ⟨k, _hKMono, hClusterSub, hOrientation⟩ :=
      exists_fixed_balanceCriticalDominantOrientation_subsequence_of_shareCluster_eq_half
        hH3 hNoExtension hClass hAt hCluster hThetaEq

    refine
      ⟨
        theta,
        hTheta,
        (fun n : ℕ => τ (k n)),
        ?_,
        hClusterSub,
        Or.inr (Or.inl ⟨hThetaEq, hOrientation⟩)
      ⟩

    intro n
    exact hData (k n)

  · rcases hCooperative with ⟨hThetaGt, hCooperativeClock⟩

    exact
      ⟨
        theta,
        hTheta,
        τ,
        hData,
        hCluster,
        Or.inr (Or.inr ⟨hThetaGt, hCooperativeClock⟩)
      ⟩

/-- Neutral formulation: either the H³ path continues smoothly, or one explicit
terminal sequence realizes a fully resolved cancellation, critical, or
cooperative balance-share regime. -/
theorem smoothContinuationExtension_or_terminal_balanceResolvedRegimeWitness
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
    H3TerminalBalanceResolvedRegimeWitness u T b := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_terminal_balanceResolvedRegimeWitness_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor specialization of the fully resolved terminal
balance-share regime witness. -/
theorem exists_terminal_balanceResolvedRegimeWitness_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalBalanceResolvedRegimeWitness
      u T (h3BKMKineticTailMidpoint a T) := by
  exact
    exists_terminal_balanceResolvedRegimeWitness_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
