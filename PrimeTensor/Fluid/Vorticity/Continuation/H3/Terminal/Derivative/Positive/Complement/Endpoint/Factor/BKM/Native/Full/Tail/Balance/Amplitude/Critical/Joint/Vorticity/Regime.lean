import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Critical.Joint.Physical.Regime
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Cancellation.Actual.Vorticity

/-!
# Critical joint physical regime with vorticity synchronization

The jointly resolved critical half-share witness has six physical regimes.  One
of them is distinguished by positive H³-energy growth: the transport-dominant
cancellation branch.  The existing BKM frequency-to-vorticity mechanism applies
at every sufficiently late positive-growth time, while the share cluster already
contains divergent characteristic frequency.

Consequently the critical transport-cancellation branch forces, on exactly the
same selected time sequence,

* divergence of the minimal common vorticity envelope, and
* divergence of actual vorticity at a selected spatial point.

The other five critical physical regimes are retained as neutral alternatives.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Critical transport-dominant cancellation enriched by synchronized minimal
and actual-vorticity divergence on the same time sequence. -/
def H3TerminalBalanceCriticalTransportCancellationVorticityAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalTransportCancellationAlong u T τ
    ∧
  Tendsto
      (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
      atTop atTop
    ∧
  ∃ y : ℕ → Point3,
    Tendsto
      (fun n : ℕ => h3ActualVorticityMaxAt u (τ n) (y n))
      atTop atTop

/-- Any critical transport-dominant cancellation share-cluster sequence inherits
minimal-envelope and actual-vorticity divergence from the positive-growth BKM
mechanism. -/
theorem h3TerminalBalanceCriticalTransportCancellationVorticityAlong_of_regime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hRegime : H3TerminalBalanceCriticalTransportCancellationAlong u T τ) :
    H3TerminalBalanceCriticalTransportCancellationVorticityAlong u T τ := by
  have hGrowth :
      ∀ᶠ n : ℕ in atTop,
        0 < deriv (velocityH3EnergyAt u) (τ n) :=
    Eventually.of_forall
      (fun n => (hRegime.2.2 n).1)

  have hEnvelope :
      Tendsto
        (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
        atTop atTop :=
    h3MinimalVorticityEnvelopeAt_tendsto_atTop_of_balanceShareCluster_positiveGrowth
      hH3
      hNoExtension
      hClass
      hb
      hAt
      hCluster
      hGrowth

  obtain ⟨y, hActual⟩ :=
    exists_actualVorticityMax_tendsto_atTop_of_minimalEnvelope_tendsto_atTop
      hEnvelope

  exact
    ⟨
      hRegime,
      hEnvelope,
      y,
      hActual
    ⟩

/-- Six-way critical classification with the positive-growth transport
cancellation branch upgraded to carry synchronized actual-vorticity escape. -/
def H3TerminalBalanceCriticalJointVorticityRegimeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong u T τ
    ∧
  (
    H3TerminalBalanceCriticalDecayCancellationAlong u T τ
      ∨ H3TerminalBalanceCriticalDecayExactAlong u T τ
      ∨ H3TerminalBalanceCriticalDecayCooperativeAlong u T τ
      ∨ H3TerminalBalanceCriticalTransportCancellationVorticityAlong u T τ
      ∨ H3TerminalBalanceCriticalTransportExactAlong u T τ
      ∨ H3TerminalBalanceCriticalTransportCooperativeAlong u T τ
  )

/-- Upgrade an already jointly resolved critical physical regime by attaching
minimal-envelope and actual-vorticity divergence in the unique positive-growth
transport-cancellation branch. -/
theorem h3TerminalBalanceCriticalJointVorticityRegimeAlong_of_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hPhysical : H3TerminalBalanceCriticalJointPhysicalRegimeAlong u T τ) :
    H3TerminalBalanceCriticalJointVorticityRegimeAlong u T τ := by
  rcases hPhysical with
    ⟨hFrontier,
      hDecayCancellation
        | hDecayExact
        | hDecayCooperative
        | hTransportCancellation
        | hTransportExact
        | hTransportCooperative⟩

  · exact
      ⟨hFrontier, Or.inl hDecayCancellation⟩

  · exact
      ⟨hFrontier, Or.inr (Or.inl hDecayExact)⟩

  · exact
      ⟨hFrontier, Or.inr (Or.inr (Or.inl hDecayCooperative))⟩

  · have hVorticity :=
      h3TerminalBalanceCriticalTransportCancellationVorticityAlong_of_regime
        hH3
        hNoExtension
        hClass
        hb
        hAt
        hCluster
        hTransportCancellation

    exact
      ⟨
        hFrontier,
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inl hVorticity)))
      ⟩

  · exact
      ⟨
        hFrontier,
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inl hTransportExact))))
      ⟩

  · exact
      ⟨
        hFrontier,
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr hTransportCooperative))))
      ⟩

/-- At critical half-share, one cofinal subsequence carries the complete six-way
joint physical classification, with actual-vorticity divergence synchronized on
the positive-growth transport-cancellation branch. -/
theorem exists_fixed_balanceCriticalJointVorticityRegime_subsequence_of_shareCluster_eq_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      H3TerminalBalanceShareClusterAlong
        u T (fun n : ℕ => τ (k n)) theta
        ∧
      H3TerminalBalanceCriticalJointVorticityRegimeAlong
        u T (fun n : ℕ => τ (k n)) := by
  obtain ⟨k, hKMono, hClusterSub, hPhysicalSub⟩ :=
    exists_fixed_balanceCriticalJointPhysicalRegime_subsequence_of_shareCluster_eq_half
      hH3
      hNoExtension
      hClass
      hAt
      hCluster
      hTheta

  have hAtSub :
      ∀ n : ℕ,
        τ (k n) ∈ Set.Ioo a T :=
    fun n => hAt (k n)

  have hVorticitySub :=
    h3TerminalBalanceCriticalJointVorticityRegimeAlong_of_physical
      hH3
      hNoExtension
      hClass
      hb
      hAtSub
      hClusterSub
      hPhysicalSub

  exact
    ⟨
      k,
      hKMono,
      hClusterSub,
      hVorticitySub
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
