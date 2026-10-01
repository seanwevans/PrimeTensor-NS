import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Resolved.Regime.Witness

/-!
# Critical half-share as the sole obstruction to two-channel magnitude cascade

The fully resolved balance-share witness leaves one genuine structural boundary.

* In the cancellation regime, one signed balance channel is the positive
  cancellation magnitude while the other is the positive canonical amplitude.
  Hence the absolute values of both physical balance derivatives carry raw,
  physical-clock, and energy-normalized divergence.
* In the cooperative regime, both negative signed balance channels already
  diverge in all three scales, so both absolute physical derivatives do as well.
* Only the critical half-share regime can leave the subordinate balance channel
  asymptotically negligible relative to the dominant amplitude.

Thus hypothetical nonextension produces either a critical half-share witness, or
an explicit terminal sequence on which both H³ balance derivatives have
simultaneous absolute raw/clock/normalized divergence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Raw, physical-clock, and energy-normalized absolute divergence of both H³
balance derivatives along one terminal sequence. -/
def H3TerminalBalanceTwoChannelAbsoluteClockCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ => |deriv (velocityH3EnergyAt u) (τ n)|)
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (T - τ n) * |deriv (velocityH3EnergyAt u) (τ n)|)
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        |deriv (velocityH3EnergyAt u) (τ n)| /
          velocityH3EnergyAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ => |velocityH3TransportDerivativeAt u (τ n)|)
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (T - τ n) * |velocityH3TransportDerivativeAt u (τ n)|)
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        |velocityH3TransportDerivativeAt u (τ n)| /
          velocityH3EnergyAt u (τ n))
      atTop atTop

private theorem absoluteClockCascade_of_signed_tendsto_atTop
    {T : ℝ}
    {τ f E : ℕ → ℝ}
    (hRaw : Tendsto f atTop atTop)
    (hClock :
      Tendsto
        (fun n : ℕ => (T - τ n) * f n)
        atTop atTop)
    (hNormalized :
      Tendsto
        (fun n : ℕ => f n / E n)
        atTop atTop) :
    Tendsto (fun n : ℕ => |f n|) atTop atTop
      ∧
    Tendsto
      (fun n : ℕ => (T - τ n) * |f n|)
      atTop atTop
      ∧
    Tendsto
      (fun n : ℕ => |f n| / E n)
      atTop atTop := by
  have hNonneg :
      ∀ᶠ n : ℕ in atTop,
        0 ≤ f n :=
    hRaw.eventually (eventually_ge_atTop (0 : ℝ))

  have hRawEq :
      ∀ᶠ n : ℕ in atTop,
        f n = |f n| := by
    filter_upwards [hNonneg] with n hn
    exact (abs_of_nonneg hn).symm

  have hClockEq :
      ∀ᶠ n : ℕ in atTop,
        (T - τ n) * f n = (T - τ n) * |f n| := by
    filter_upwards [hNonneg] with n hn
    rw [abs_of_nonneg hn]

  have hNormalizedEq :
      ∀ᶠ n : ℕ in atTop,
        f n / E n = |f n| / E n := by
    filter_upwards [hNonneg] with n hn
    rw [abs_of_nonneg hn]

  exact
    ⟨
      hRaw.congr' hRawEq,
      hClock.congr' hClockEq,
      hNormalized.congr' hNormalizedEq
    ⟩

/-- A resolved cancellation regime forces simultaneous absolute divergence of
both physical balance derivatives. -/
theorem h3TerminalBalanceTwoChannelAbsoluteClockCascadeAlong_of_cancellationResolved
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T theta : ℝ}
    {τ : ℕ → ℝ}
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hResolved :
      H3TerminalBalanceCancellationResolvedClockCascadeAlong u T τ) :
    H3TerminalBalanceTwoChannelAbsoluteClockCascadeAlong u T τ := by
  rcases hResolved with hGrowth | hTransport

  · rcases hGrowth with
      ⟨hIdentities, hEnergyRaw, hEnergyClock, hEnergyNormalized,
        _hEnvelope, _hActual⟩

    have hEnergyAbs :=
      absoluteClockCascade_of_signed_tendsto_atTop
        (T := T)
        (τ := τ)
        (f := fun n : ℕ => deriv (velocityH3EnergyAt u) (τ n))
        (E := fun n : ℕ => velocityH3EnergyAt u (τ n))
        hEnergyRaw hEnergyClock hEnergyNormalized

    have hTransportRaw :
        Tendsto
          (fun n : ℕ => - velocityH3TransportDerivativeAt u (τ n))
          atTop atTop := by
      have h := hCluster.1.2.1
      have hEq :
          (fun n : ℕ => h3TerminalBalanceAmplitudeAt u (τ n))
            =
          (fun n : ℕ => - velocityH3TransportDerivativeAt u (τ n)) := by
        funext n
        exact (hIdentities n).2
      rw [hEq] at h
      exact h

    have hTransportClock :
        Tendsto
          (fun n : ℕ =>
            (T - τ n) * (- velocityH3TransportDerivativeAt u (τ n)))
          atTop atTop := by
      have h := hCluster.1.2.2.1
      have hEq :
          (fun n : ℕ =>
            (T - τ n) * h3TerminalBalanceAmplitudeAt u (τ n))
            =
          (fun n : ℕ =>
            (T - τ n) * (- velocityH3TransportDerivativeAt u (τ n))) := by
        funext n
        rw [(hIdentities n).2]
      rw [hEq] at h
      exact h

    have hTransportNormalized :
        Tendsto
          (fun n : ℕ =>
            (- velocityH3TransportDerivativeAt u (τ n)) /
              velocityH3EnergyAt u (τ n))
          atTop atTop := by
      have h := hCluster.1.2.2.2.1
      have hEq :
          (fun n : ℕ =>
            h3TerminalBalanceAmplitudeAt u (τ n) /
              velocityH3EnergyAt u (τ n))
            =
          (fun n : ℕ =>
            (- velocityH3TransportDerivativeAt u (τ n)) /
              velocityH3EnergyAt u (τ n)) := by
        funext n
        rw [(hIdentities n).2]
      rw [hEq] at h
      exact h

    have hTransportAbsNeg :=
      absoluteClockCascade_of_signed_tendsto_atTop
        (T := T)
        (τ := τ)
        (f := fun n : ℕ => - velocityH3TransportDerivativeAt u (τ n))
        (E := fun n : ℕ => velocityH3EnergyAt u (τ n))
        hTransportRaw hTransportClock hTransportNormalized

    have hTransportAbs :
        Tendsto
            (fun n : ℕ => |velocityH3TransportDerivativeAt u (τ n)|)
            atTop atTop
          ∧
        Tendsto
            (fun n : ℕ =>
              (T - τ n) * |velocityH3TransportDerivativeAt u (τ n)|)
            atTop atTop
          ∧
        Tendsto
            (fun n : ℕ =>
              |velocityH3TransportDerivativeAt u (τ n)| /
                velocityH3EnergyAt u (τ n))
            atTop atTop := by
      simpa only [abs_neg] using hTransportAbsNeg

    exact
      ⟨
        hEnergyAbs.1,
        hEnergyAbs.2.1,
        hEnergyAbs.2.2,
        hTransportAbs.1,
        hTransportAbs.2.1,
        hTransportAbs.2.2
      ⟩

  · rcases hTransport with
      ⟨hIdentities, hTransportRaw, hTransportClock, hTransportNormalized⟩

    have hTransportAbs :=
      absoluteClockCascade_of_signed_tendsto_atTop
        (T := T)
        (τ := τ)
        (f := fun n : ℕ => velocityH3TransportDerivativeAt u (τ n))
        (E := fun n : ℕ => velocityH3EnergyAt u (τ n))
        hTransportRaw hTransportClock hTransportNormalized

    have hEnergyRaw :
        Tendsto
          (fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ n))
          atTop atTop := by
      have h := hCluster.1.2.1
      have hEq :
          (fun n : ℕ => h3TerminalBalanceAmplitudeAt u (τ n))
            =
          (fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ n)) := by
        funext n
        exact (hIdentities n).2
      rw [hEq] at h
      exact h

    have hEnergyClock :
        Tendsto
          (fun n : ℕ =>
            (T - τ n) * (- deriv (velocityH3EnergyAt u) (τ n)))
          atTop atTop := by
      have h := hCluster.1.2.2.1
      have hEq :
          (fun n : ℕ =>
            (T - τ n) * h3TerminalBalanceAmplitudeAt u (τ n))
            =
          (fun n : ℕ =>
            (T - τ n) * (- deriv (velocityH3EnergyAt u) (τ n))) := by
        funext n
        rw [(hIdentities n).2]
      rw [hEq] at h
      exact h

    have hEnergyNormalized :
        Tendsto
          (fun n : ℕ =>
            (- deriv (velocityH3EnergyAt u) (τ n)) /
              velocityH3EnergyAt u (τ n))
          atTop atTop := by
      have h := hCluster.1.2.2.2.1
      have hEq :
          (fun n : ℕ =>
            h3TerminalBalanceAmplitudeAt u (τ n) /
              velocityH3EnergyAt u (τ n))
            =
          (fun n : ℕ =>
            (- deriv (velocityH3EnergyAt u) (τ n)) /
              velocityH3EnergyAt u (τ n)) := by
        funext n
        rw [(hIdentities n).2]
      rw [hEq] at h
      exact h

    have hEnergyAbsNeg :=
      absoluteClockCascade_of_signed_tendsto_atTop
        (T := T)
        (τ := τ)
        (f := fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ n))
        (E := fun n : ℕ => velocityH3EnergyAt u (τ n))
        hEnergyRaw hEnergyClock hEnergyNormalized

    have hEnergyAbs :
        Tendsto
            (fun n : ℕ => |deriv (velocityH3EnergyAt u) (τ n)|)
            atTop atTop
          ∧
        Tendsto
            (fun n : ℕ =>
              (T - τ n) * |deriv (velocityH3EnergyAt u) (τ n)|)
            atTop atTop
          ∧
        Tendsto
            (fun n : ℕ =>
              |deriv (velocityH3EnergyAt u) (τ n)| /
                velocityH3EnergyAt u (τ n))
            atTop atTop := by
      simpa only [abs_neg] using hEnergyAbsNeg

    exact
      ⟨
        hEnergyAbs.1,
        hEnergyAbs.2.1,
        hEnergyAbs.2.2,
        hTransportAbs.1,
        hTransportAbs.2.1,
        hTransportAbs.2.2
      ⟩

/-- The cooperative regime also forces simultaneous absolute divergence of both
physical balance derivatives. -/
theorem h3TerminalBalanceTwoChannelAbsoluteClockCascadeAlong_of_cooperative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    {τ : ℕ → ℝ}
    (hCooperative : H3TerminalBalanceCooperativeClockCascadeAlong u T τ) :
    H3TerminalBalanceTwoChannelAbsoluteClockCascadeAlong u T τ := by
  rcases hCooperative with
    ⟨_hSubRaw, _hSubClock, _hSubNormalized,
      hEnergyRaw, hEnergyClock, hEnergyNormalized,
      hTransportRaw, hTransportClock, hTransportNormalized⟩

  have hEnergyAbsNeg :=
    absoluteClockCascade_of_signed_tendsto_atTop
      (T := T)
      (τ := τ)
      (f := fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ n))
      (E := fun n : ℕ => velocityH3EnergyAt u (τ n))
      hEnergyRaw hEnergyClock hEnergyNormalized

  have hTransportAbsNeg :=
    absoluteClockCascade_of_signed_tendsto_atTop
      (T := T)
      (τ := τ)
      (f := fun n : ℕ => - velocityH3TransportDerivativeAt u (τ n))
      (E := fun n : ℕ => velocityH3EnergyAt u (τ n))
      hTransportRaw hTransportClock hTransportNormalized

  have hEnergyAbs :
      Tendsto
          (fun n : ℕ => |deriv (velocityH3EnergyAt u) (τ n)|)
          atTop atTop
        ∧
      Tendsto
          (fun n : ℕ =>
            (T - τ n) * |deriv (velocityH3EnergyAt u) (τ n)|)
          atTop atTop
        ∧
      Tendsto
          (fun n : ℕ =>
            |deriv (velocityH3EnergyAt u) (τ n)| /
              velocityH3EnergyAt u (τ n))
          atTop atTop := by
    simpa only [abs_neg] using hEnergyAbsNeg

  have hTransportAbs :
      Tendsto
          (fun n : ℕ => |velocityH3TransportDerivativeAt u (τ n)|)
          atTop atTop
        ∧
      Tendsto
          (fun n : ℕ =>
            (T - τ n) * |velocityH3TransportDerivativeAt u (τ n)|)
          atTop atTop
        ∧
      Tendsto
          (fun n : ℕ =>
            |velocityH3TransportDerivativeAt u (τ n)| /
              velocityH3EnergyAt u (τ n))
          atTop atTop := by
    simpa only [abs_neg] using hTransportAbsNeg

  exact
    ⟨
      hEnergyAbs.1,
      hEnergyAbs.2.1,
      hEnergyAbs.2.2,
      hTransportAbs.1,
      hTransportAbs.2.1,
      hTransportAbs.2.2
    ⟩

/-- One terminal witness in which the critical half-share is the only possible
obstruction to simultaneous two-channel absolute divergence. -/
def H3TerminalBalanceCriticalOrTwoChannelWitness
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
          theta = (1 : ℝ) / 2
            ∧
          H3TerminalBalanceCriticalResolvedClockCascadeAlong u T τ
        )
          ∨
        (
          theta ≠ (1 : ℝ) / 2
            ∧
          H3TerminalBalanceTwoChannelAbsoluteClockCascadeAlong u T τ
        )
      )

/-- Under hypothetical nonextension, critical half-share is the sole unresolved
obstruction to simultaneous absolute divergence of both balance derivatives. -/
theorem exists_terminal_balanceCriticalOrTwoChannelWitness_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    H3TerminalBalanceCriticalOrTwoChannelWitness u T b := by
  rcases
    exists_terminal_balanceResolvedRegimeWitness_of_noH3PathExtension
      hH3 hNoExtension hClass hb
    with ⟨theta, hTheta, τ, hData, hCluster, hRegime⟩

  rcases hRegime with hCancellation | hCritical | hCooperative

  · rcases hCancellation with ⟨hThetaLt, hResolved⟩

    have hTwoChannel :=
      h3TerminalBalanceTwoChannelAbsoluteClockCascadeAlong_of_cancellationResolved
        hCluster hResolved

    exact
      ⟨
        theta,
        hTheta,
        τ,
        hData,
        hCluster,
        Or.inr
          ⟨
            by linarith,
            hTwoChannel
          ⟩
      ⟩

  · rcases hCritical with ⟨hThetaEq, hResolved⟩

    exact
      ⟨
        theta,
        hTheta,
        τ,
        hData,
        hCluster,
        Or.inl ⟨hThetaEq, hResolved⟩
      ⟩

  · rcases hCooperative with ⟨hThetaGt, hCooperative⟩

    have hTwoChannel :=
      h3TerminalBalanceTwoChannelAbsoluteClockCascadeAlong_of_cooperative
        hCooperative

    exact
      ⟨
        theta,
        hTheta,
        τ,
        hData,
        hCluster,
        Or.inr
          ⟨
            by linarith,
            hTwoChannel
          ⟩
      ⟩

/-- Neutral continuation alternative exposing the critical obstruction directly. -/
theorem smoothContinuationExtension_or_terminal_balanceCriticalOrTwoChannelWitness
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
    H3TerminalBalanceCriticalOrTwoChannelWitness u T b := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_terminal_balanceCriticalOrTwoChannelWitness_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Midpoint-anchor specialization of the critical obstruction theorem. -/
theorem exists_terminal_balanceCriticalOrTwoChannelWitness_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalBalanceCriticalOrTwoChannelWitness
      u T (h3BKMKineticTailMidpoint a T) := by
  exact
    exists_terminal_balanceCriticalOrTwoChannelWitness_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
