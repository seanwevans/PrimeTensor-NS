import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCriticalJointVorticityRegime

/-!
# Critical half-share reduction under a terminal vorticity ceiling

The jointly synchronized critical witness has six physical regimes.  The
transport-dominant cancellation branch is the unique positive-H³-growth branch
and therefore carries minimal-envelope divergence by the existing BKM mechanism.

If the minimal common vorticity envelope is uniformly bounded on one strict
terminal tail `(b,T)`, that branch is impossible on any selected sequence tending
to `T`.  The remaining critical alternative therefore consists of the five
non-positive-growth regimes:

* decay-dominant cancellation;
* decay-dominant exact balance;
* decay-dominant cooperative balance;
* transport-dominant exact balance;
* transport-dominant cooperative balance.

This is a conditional reduction only; no assertion is made that the terminal
vorticity ceiling holds for an arbitrary solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Critical joint classification after excluding the positive-growth
transport-cancellation branch by a terminal minimal-vorticity ceiling. -/
def H3TerminalBalanceCriticalVorticityCeilingReducedAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong u T τ
    ∧
  (
    H3TerminalBalanceCriticalDecayCancellationAlong u T τ
      ∨ H3TerminalBalanceCriticalDecayExactAlong u T τ
      ∨ H3TerminalBalanceCriticalDecayCooperativeAlong u T τ
      ∨ H3TerminalBalanceCriticalTransportExactAlong u T τ
      ∨ H3TerminalBalanceCriticalTransportCooperativeAlong u T τ
  )

/-- A minimal-vorticity ceiling on `(b,T)` excludes the synchronized critical
transport-cancellation branch, because that branch forces the minimal envelope
to diverge along the same terminal sequence. -/
theorem h3TerminalBalanceCriticalVorticityCeilingReducedAlong_of_jointVorticity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b theta M : ℝ}
    {τ : ℕ → ℝ}
    (hb : b ∈ Set.Ioo a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hCeiling :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          h3MinimalVorticityEnvelopeAt u t ≤ M)
    (hJoint : H3TerminalBalanceCriticalJointVorticityRegimeAlong u T τ) :
    H3TerminalBalanceCriticalVorticityCeilingReducedAlong u T τ := by
  rcases hJoint with
    ⟨hFrontier,
      hDecayCancellation
        | hDecayExact
        | hDecayCooperative
        | hTransportCancellation
        | hTransportExact
        | hTransportCooperative⟩

  · exact ⟨hFrontier, Or.inl hDecayCancellation⟩

  · exact ⟨hFrontier, Or.inr (Or.inl hDecayExact)⟩

  · exact ⟨hFrontier, Or.inr (Or.inr (Or.inl hDecayCooperative))⟩

  · have hEventuallyPastB :
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
      hTransportCancellation.2.1.eventually
        (eventually_gt_atTop M)

    exfalso
    obtain ⟨n, hLe, hGt⟩ :=
      (hEventuallyCeiling.and hEventuallyAbove).exists
    exact (not_lt_of_ge hLe) hGt

  · exact
      ⟨
        hFrontier,
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inl hTransportExact)))
      ⟩

  · exact
      ⟨
        hFrontier,
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr hTransportCooperative)))
      ⟩

/-- Under a uniform minimal-vorticity ceiling on one strict terminal tail, the
critical half-share extraction can be chosen in one of only the five
non-positive-growth physical regimes. -/
theorem exists_fixed_balanceCriticalVorticityCeilingReduced_subsequence_of_shareCluster_eq_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b theta M : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2)
    (hCeiling :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          h3MinimalVorticityEnvelopeAt u t ≤ M) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      H3TerminalBalanceShareClusterAlong
        u T (fun n : ℕ => τ (k n)) theta
        ∧
      H3TerminalBalanceCriticalVorticityCeilingReducedAlong
        u T (fun n : ℕ => τ (k n)) := by
  obtain ⟨k, hKMono, hClusterSub, hJointSub⟩ :=
    exists_fixed_balanceCriticalJointVorticityRegime_subsequence_of_shareCluster_eq_half
      hH3
      hNoExtension
      hClass
      hb
      hAt
      hCluster
      hTheta

  have hAtSub :
      ∀ n : ℕ,
        τ (k n) ∈ Set.Ioo a T :=
    fun n => hAt (k n)

  have hReduced :=
    h3TerminalBalanceCriticalVorticityCeilingReducedAlong_of_jointVorticity
      hb
      hAtSub
      hClusterSub
      hCeiling
      hJointSub

  exact
    ⟨
      k,
      hKMono,
      hClusterSub,
      hReduced
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
