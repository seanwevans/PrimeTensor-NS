import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Share.Regime.Witness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Cancellation.Orientation

/-!
# Critical half-share orientation for the balance-amplitude cluster

At the critical dissipation share `theta = 1/2`, the subordinate signed balance
channel is asymptotically negligible relative to the canonical amplitude:

`S / B -> 0`.

This file freezes which signed channel realizes the dominant maximum along a
cofinal subsequence.  The selected dominant channel is then exactly the
canonical balance amplitude at every selected time, so it inherits the full
raw, physical-clock, and energy-normalized amplitude divergence.  The other
channel remains subordinate and negligible relative to the dominant amplitude.

No sign conclusion is imposed on the subordinate channel in the critical
regime.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Critical cluster with the negative H³ energy derivative frozen as the
canonical dominant balance channel. -/
def H3TerminalBalanceCriticalDecayDominantClockCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  (∀ n : ℕ,
    h3TerminalBalanceAmplitudeAt u (τ n)
        = - deriv (velocityH3EnergyAt u) (τ n)
      ∧
    h3TerminalBalanceSubordinateChannelAt u (τ n)
        = - velocityH3TransportDerivativeAt u (τ n))
    ∧
  Tendsto
      (fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (T - τ n) * (- deriv (velocityH3EnergyAt u) (τ n)))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (- deriv (velocityH3EnergyAt u) (τ n)) /
          velocityH3EnergyAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          h3TerminalBalanceAmplitudeAt u (τ n))
      atTop (𝓝 (0 : ℝ))

/-- Critical cluster with the negative H³ transport derivative frozen as the
canonical dominant balance channel. -/
def H3TerminalBalanceCriticalTransportDominantClockCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  (∀ n : ℕ,
    h3TerminalBalanceAmplitudeAt u (τ n)
        = - velocityH3TransportDerivativeAt u (τ n)
      ∧
    h3TerminalBalanceSubordinateChannelAt u (τ n)
        = - deriv (velocityH3EnergyAt u) (τ n))
    ∧
  Tendsto
      (fun n : ℕ => - velocityH3TransportDerivativeAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (T - τ n) * (- velocityH3TransportDerivativeAt u (τ n)))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (- velocityH3TransportDerivativeAt u (τ n)) /
          velocityH3EnergyAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          h3TerminalBalanceAmplitudeAt u (τ n))
      atTop (𝓝 (0 : ℝ))

/-- At the critical half-share, a cofinal subsequence freezes one dominant
balance channel.  That channel inherits the complete raw/clock/normalized
amplitude cascade, while the subordinate channel remains negligible relative
to the amplitude. -/
theorem exists_fixed_balanceCriticalDominantOrientation_subsequence_of_shareCluster_eq_half
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
      (
        H3TerminalBalanceCriticalDecayDominantClockCascadeAlong
          u T (fun n : ℕ => τ (k n))
          ∨
        H3TerminalBalanceCriticalTransportDominantClockCascadeAlong
          u T (fun n : ℕ => τ (k n))
      ) := by
  classical

  let channel : ℕ → Bool :=
    fun n =>
      decide
        ((- deriv (velocityH3EnergyAt u) (τ n))
          ≤ (- velocityH3TransportDerivativeAt u (τ n)))

  have hFrequentlySomeChannel :
      ∃ᶠ n : ℕ in atTop,
        ∃ q : Bool, channel n = q :=
    Frequently.of_forall
      (fun n => ⟨channel n, rfl⟩)

  obtain ⟨q, hChannelFrequently⟩ :=
    (Filter.frequently_exists).1 hFrequentlySomeChannel

  obtain ⟨k, hKMono, hChannelFixed⟩ :=
    extraction_of_frequently_atTop hChannelFrequently

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

  have hSubordinateZero :
      Tendsto
        (fun n : ℕ =>
          h3TerminalBalanceSubordinateChannelAt u (τ (k n)) /
            h3TerminalBalanceAmplitudeAt u (τ (k n)))
        atTop
        (𝓝 (0 : ℝ)) :=
    h3TerminalBalanceSubordinateRatio_tendsto_zero_of_shareCluster_eq_half
      hH3 hClass hAtSub hClusterSub hTheta

  cases q with
  | false =>
      refine ⟨k, hKMono, hClusterSub, Or.inl ?_⟩

      have hIdentities :
          ∀ n : ℕ,
            h3TerminalBalanceAmplitudeAt u (τ (k n))
                = - deriv (velocityH3EnergyAt u) (τ (k n))
              ∧
            h3TerminalBalanceSubordinateChannelAt u (τ (k n))
                = - velocityH3TransportDerivativeAt u (τ (k n)) := by
        intro n
        have hNotOrder :
            ¬
              (- deriv (velocityH3EnergyAt u) (τ (k n)))
                ≤ (- velocityH3TransportDerivativeAt u (τ (k n))) := by
          have hFixed := hChannelFixed n
          simpa [channel] using hFixed

        have hOrder :
            (- velocityH3TransportDerivativeAt u (τ (k n)))
              ≤ (- deriv (velocityH3EnergyAt u) (τ (k n))) :=
          le_of_lt (lt_of_not_ge hNotOrder)

        constructor
        · rw [h3TerminalBalanceAmplitudeAt]
          exact max_eq_left hOrder
        · unfold h3TerminalBalanceSubordinateChannelAt
          exact min_eq_right hOrder

      have hRaw :
          Tendsto
            (fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ (k n)))
            atTop atTop := by
        have h := hClusterSub.1.2.1
        have hEq :
            (fun n : ℕ => h3TerminalBalanceAmplitudeAt u (τ (k n)))
              =
            (fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ (k n))) := by
          funext n
          exact (hIdentities n).1
        rw [hEq] at h
        exact h

      have hClock :
          Tendsto
            (fun n : ℕ =>
              (T - τ (k n)) *
                (- deriv (velocityH3EnergyAt u) (τ (k n))))
            atTop atTop := by
        have h := hClusterSub.1.2.2.1
        have hEq :
            (fun n : ℕ =>
              (T - τ (k n)) *
                h3TerminalBalanceAmplitudeAt u (τ (k n)))
              =
            (fun n : ℕ =>
              (T - τ (k n)) *
                (- deriv (velocityH3EnergyAt u) (τ (k n)))) := by
          funext n
          rw [(hIdentities n).1]
        rw [hEq] at h
        exact h

      have hNormalized :
          Tendsto
            (fun n : ℕ =>
              (- deriv (velocityH3EnergyAt u) (τ (k n))) /
                velocityH3EnergyAt u (τ (k n)))
            atTop atTop := by
        have h := hClusterSub.1.2.2.2.1
        have hEq :
            (fun n : ℕ =>
              h3TerminalBalanceAmplitudeAt u (τ (k n)) /
                velocityH3EnergyAt u (τ (k n)))
              =
            (fun n : ℕ =>
              (- deriv (velocityH3EnergyAt u) (τ (k n))) /
                velocityH3EnergyAt u (τ (k n))) := by
          funext n
          rw [(hIdentities n).1]
        rw [hEq] at h
        exact h

      exact
        ⟨
          hIdentities,
          hRaw,
          hClock,
          hNormalized,
          hSubordinateZero
        ⟩

  | true =>
      refine ⟨k, hKMono, hClusterSub, Or.inr ?_⟩

      have hIdentities :
          ∀ n : ℕ,
            h3TerminalBalanceAmplitudeAt u (τ (k n))
                = - velocityH3TransportDerivativeAt u (τ (k n))
              ∧
            h3TerminalBalanceSubordinateChannelAt u (τ (k n))
                = - deriv (velocityH3EnergyAt u) (τ (k n)) := by
        intro n
        have hOrder :
            (- deriv (velocityH3EnergyAt u) (τ (k n)))
              ≤ (- velocityH3TransportDerivativeAt u (τ (k n))) := by
          have hFixed := hChannelFixed n
          simpa [channel] using hFixed

        constructor
        · rw [h3TerminalBalanceAmplitudeAt]
          exact max_eq_right hOrder
        · unfold h3TerminalBalanceSubordinateChannelAt
          exact min_eq_left hOrder

      have hRaw :
          Tendsto
            (fun n : ℕ => - velocityH3TransportDerivativeAt u (τ (k n)))
            atTop atTop := by
        have h := hClusterSub.1.2.1
        have hEq :
            (fun n : ℕ => h3TerminalBalanceAmplitudeAt u (τ (k n)))
              =
            (fun n : ℕ => - velocityH3TransportDerivativeAt u (τ (k n))) := by
          funext n
          exact (hIdentities n).1
        rw [hEq] at h
        exact h

      have hClock :
          Tendsto
            (fun n : ℕ =>
              (T - τ (k n)) *
                (- velocityH3TransportDerivativeAt u (τ (k n))))
            atTop atTop := by
        have h := hClusterSub.1.2.2.1
        have hEq :
            (fun n : ℕ =>
              (T - τ (k n)) *
                h3TerminalBalanceAmplitudeAt u (τ (k n)))
              =
            (fun n : ℕ =>
              (T - τ (k n)) *
                (- velocityH3TransportDerivativeAt u (τ (k n)))) := by
          funext n
          rw [(hIdentities n).1]
        rw [hEq] at h
        exact h

      have hNormalized :
          Tendsto
            (fun n : ℕ =>
              (- velocityH3TransportDerivativeAt u (τ (k n))) /
                velocityH3EnergyAt u (τ (k n)))
            atTop atTop := by
        have h := hClusterSub.1.2.2.2.1
        have hEq :
            (fun n : ℕ =>
              h3TerminalBalanceAmplitudeAt u (τ (k n)) /
                velocityH3EnergyAt u (τ (k n)))
              =
            (fun n : ℕ =>
              (- velocityH3TransportDerivativeAt u (τ (k n))) /
                velocityH3EnergyAt u (τ (k n))) := by
          funext n
          rw [(hIdentities n).1]
        rw [hEq] at h
        exact h

      exact
        ⟨
          hIdentities,
          hRaw,
          hClock,
          hNormalized,
          hSubordinateZero
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
