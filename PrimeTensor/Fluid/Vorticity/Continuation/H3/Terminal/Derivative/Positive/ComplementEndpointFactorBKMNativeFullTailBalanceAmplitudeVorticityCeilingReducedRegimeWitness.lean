import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCriticalVorticityCeilingReduction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeResolvedRegimeWitness

/-!
# Global balance-share reduction under a terminal vorticity ceiling

A uniform bound for the minimal common vorticity envelope on one strict terminal
tail excludes every resolved balance-share branch with positive H³ energy
growth.

For hypothetical nonextension this leaves three share regimes:

* below half: only the positive-transport cancellation orientation survives;
* exactly half: only the five critical non-positive-growth regimes survive;
* above half: the cooperative balance cascade is unchanged.

The result is conditional on the stated terminal vorticity ceiling and does not
assert that such a ceiling holds for arbitrary solutions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The below-half cancellation orientation surviving a bounded terminal
minimal-vorticity envelope: transport grows positively while the negative
energy derivative remains the canonical amplitude. -/
def H3TerminalBalanceCancellationTransportPositiveClockCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
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

/-- A terminal witness after all positive-H³-growth balance branches have been
excluded by a uniform minimal-vorticity ceiling on the chosen strict tail. -/
def H3TerminalBalanceVorticityCeilingReducedRegimeWitness
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
          H3TerminalBalanceCancellationTransportPositiveClockCascadeAlong
            u T τ
        )
          ∨
        (
          theta = (1 : ℝ) / 2
            ∧
          H3TerminalBalanceCriticalVorticityCeilingReducedAlong u T τ
        )
          ∨
        (
          (1 : ℝ) / 2 < theta
            ∧
          H3TerminalBalanceCooperativeClockCascadeAlong u T τ
        )
      )

private theorem not_minimalVorticityEnvelope_tendsto_atTop_of_terminal_ceiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b theta M : ℝ}
    {τ : ℕ → ℝ}
    (hb : b ∈ Set.Ioo a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hCeiling :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          h3MinimalVorticityEnvelopeAt u t ≤ M) :
    ¬ Tendsto
        (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
        atTop atTop := by
  intro hEnvelope

  have hEventuallyPastB :
      ∀ᶠ n : ℕ in atTop,
        b < τ n :=
    (tendsto_order.1 hCluster.1.1).1 b hb.2

  have hEventuallyCeiling :
      ∀ᶠ n : ℕ in atTop,
        h3MinimalVorticityEnvelopeAt u (τ n) ≤ M := by
    filter_upwards [hEventuallyPastB] with n hn
    exact hCeiling (τ n) ⟨hn, (hAt n).2⟩

  have hEventuallyAbove :
      ∀ᶠ n : ℕ in atTop,
        M < h3MinimalVorticityEnvelopeAt u (τ n) :=
    hEnvelope.eventually (eventually_gt_atTop M)

  obtain ⟨n, hLe, hGt⟩ :=
    (hEventuallyCeiling.and hEventuallyAbove).exists
  exact (not_lt_of_ge hLe) hGt

/-- Under hypothetical nonextension and a uniform minimal-vorticity ceiling on
one strict terminal tail, the complete balance-share witness can be chosen with
all positive-H³-growth branches removed. -/
theorem exists_terminal_balanceVorticityCeilingReducedRegimeWitness_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hCeiling :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          h3MinimalVorticityEnvelopeAt u t ≤ M) :
    H3TerminalBalanceVorticityCeilingReducedRegimeWitness u T b := by
  rcases
    exists_terminal_balanceResolvedRegimeWitness_of_noH3PathExtension
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

  · rcases hCancellation with ⟨hThetaLt, hResolved⟩
    rcases hResolved with hGrowth | hTransport

    · have hImpossible :=
        not_minimalVorticityEnvelope_tendsto_atTop_of_terminal_ceiling
          hb hAt hCluster hCeiling
      exact False.elim (hImpossible hGrowth.2.2.2.2.1)

    · exact
        ⟨
          theta,
          hTheta,
          τ,
          hData,
          hCluster,
          Or.inl ⟨hThetaLt, hTransport⟩
        ⟩

  · rcases hCritical with ⟨hThetaEq, _hResolvedCritical⟩

    obtain ⟨k, _hKMono, hClusterSub, hCriticalReduced⟩ :=
      exists_fixed_balanceCriticalVorticityCeilingReduced_subsequence_of_shareCluster_eq_half
        hH3
        hNoExtension
        hClass
        hb
        hAt
        hCluster
        hThetaEq
        hCeiling

    refine
      ⟨
        theta,
        hTheta,
        (fun n : ℕ => τ (k n)),
        ?_,
        hClusterSub,
        Or.inr (Or.inl ⟨hThetaEq, hCriticalReduced⟩)
      ⟩

    intro n
    exact hData (k n)

  · rcases hCooperative with ⟨hThetaGt, hCooperative⟩
    exact
      ⟨
        theta,
        hTheta,
        τ,
        hData,
        hCluster,
        Or.inr (Or.inr ⟨hThetaGt, hCooperative⟩)
      ⟩

/-- Neutral formulation under the same terminal minimal-vorticity ceiling:
either the H³ path continues smoothly, or the reduced non-positive-growth
balance-share witness occurs. -/
theorem smoothContinuationExtension_or_terminal_balanceVorticityCeilingReducedRegimeWitness
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hCeiling :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          h3MinimalVorticityEnvelopeAt u t ≤ M) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    H3TerminalBalanceVorticityCeilingReducedRegimeWitness u T b := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_terminal_balanceVorticityCeilingReducedRegimeWitness_of_noH3PathExtension
          hH3 hExtension hClass hb hCeiling)

/-- Canonical midpoint-anchor specialization of the vorticity-ceiling reduced
terminal balance-share witness. -/
theorem exists_terminal_balanceVorticityCeilingReducedRegimeWitness_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hCeiling :
      ∀ t : ℝ,
        t ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T →
          h3MinimalVorticityEnvelopeAt u t ≤ M) :
    H3TerminalBalanceVorticityCeilingReducedRegimeWitness
      u T (h3BKMKineticTailMidpoint a T) := by
  exact
    exists_terminal_balanceVorticityCeilingReducedRegimeWitness_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)
      hCeiling

end

end Euclidean
end Bridge
end PrimeTensor
