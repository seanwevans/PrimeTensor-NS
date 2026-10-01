import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Cancellation.Clock.Rates

/-!
# Quantitative trichotomy for the balance-amplitude share cluster

The asymptotic dissipation share `theta` determines three genuinely different
terminal balance regimes.

* `theta < 1/2`: the subordinate signed channel is opposite in sign to the
  dominant amplitude.  The cancellation magnitude carries raw, physical-clock,
  and energy-normalized divergence.
* `theta = 1/2`: the subordinate channel is negligible relative to the dominant
  amplitude.
* `theta > 1/2`: the subordinate channel is a fixed positive fraction of the
  dominant amplitude.  Hence the subordinate channel itself, and therefore both
  signed balance channels `-E'` and `-Transport`, carry raw, physical-clock, and
  energy-normalized divergence on the same sequence.

The cooperative regime is branch-free: no choice of dominant channel or further
subsequence extraction is required.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem tendsto_atTop_of_eventually_const_mul_le_cooperative
    {f g : ℕ → ℝ}
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hg : Tendsto g atTop atTop)
    (hLower : ∀ᶠ n : ℕ in atTop, delta * g n ≤ f n) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  let R : ℝ := M / delta
  have hEventuallyG :
      ∀ᶠ n : ℕ in atTop, R ≤ g n :=
    hg.eventually (eventually_ge_atTop R)
  filter_upwards [hEventuallyG, hLower] with n hGn hFn
  have hMLe : M ≤ delta * g n := by
    dsimp only [R] at hGn
    simpa only [mul_comm] using ((div_le_iff₀ hdelta).1 hGn)
  exact le_trans hMLe hFn

private theorem tendsto_atTop_of_eventually_le_cooperative
    {f g : ℕ → ℝ}
    (hg : Tendsto g atTop atTop)
    (hLower : ∀ᶠ n : ℕ in atTop, g n ≤ f n) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  have hEventuallyG :
      ∀ᶠ n : ℕ in atTop, M ≤ g n :=
    hg.eventually (eventually_ge_atTop M)
  filter_upwards [hEventuallyG, hLower] with n hMn hFn
  exact le_trans hMn hFn

/-- Raw, physical-clock, and normalized divergence of the cancellation
magnitude. -/
def H3TerminalBalanceCancellationClockCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ => h3TerminalBalanceCancellationMagnitudeAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (T - τ n) * h3TerminalBalanceCancellationMagnitudeAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
          velocityH3EnergyAt u (τ n))
      atTop atTop

/-- In the cooperative regime, the subordinate channel and both signed balance
channels carry raw, physical-clock, and normalized divergence. -/
def H3TerminalBalanceCooperativeClockCascadeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ => h3TerminalBalanceSubordinateChannelAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (T - τ n) * h3TerminalBalanceSubordinateChannelAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          velocityH3EnergyAt u (τ n))
      atTop atTop
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

/-- The existing three cancellation divergences form one reusable cascade. -/
theorem h3TerminalBalanceCancellationClockCascadeAlong_of_shareCluster_lt_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta < (1 : ℝ) / 2) :
    H3TerminalBalanceCancellationClockCascadeAlong u T τ := by
  exact
    ⟨
      h3TerminalBalanceCancellationMagnitudeAt_tendsto_atTop_of_shareCluster_lt_half
        hH3 hClass hAt hCluster hTheta,
      h3TerminalBalanceCancellationMagnitudePhysicalClock_tendsto_atTop_of_shareCluster_lt_half
        hH3 hClass hAt hCluster hTheta,
      h3TerminalBalanceCancellationMagnitudeNormalizedRate_tendsto_atTop_of_shareCluster_lt_half
        hH3 hClass hAt hCluster hTheta
    ⟩

/-- Strictly above half-share, the subordinate channel itself diverges. -/
theorem h3TerminalBalanceSubordinateChannelAt_tendsto_atTop_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    Tendsto
      (fun n : ℕ => h3TerminalBalanceSubordinateChannelAt u (τ n))
      atTop atTop := by
  let kappa : ℝ := 2 * theta - 1
  let delta : ℝ := kappa / 2

  have hkappaPos : 0 < kappa := by
    dsimp only [kappa]
    linarith

  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact div_pos hkappaPos (by norm_num)

  have hdeltaLt : delta < kappa := by
    dsimp only [delta]
    linarith

  have hRatio :
      Tendsto
        (fun n : ℕ =>
          h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
        atTop (𝓝 kappa) := by
    simpa only [kappa] using
      h3TerminalBalanceSubordinateRatio_tendsto_of_shareCluster
        hH3 hClass hAt hCluster

  have hRatioLower :
      ∀ᶠ n : ℕ in atTop,
        delta <
          h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n) :=
    hRatio.eventually (Ioi_mem_nhds hdeltaLt)

  have hAmplitudePos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hCluster.1.2.1.eventually (eventually_gt_atTop (0 : ℝ))

  have hLower :
      ∀ᶠ n : ℕ in atTop,
        delta * h3TerminalBalanceAmplitudeAt u (τ n)
          ≤ h3TerminalBalanceSubordinateChannelAt u (τ n) := by
    filter_upwards [hRatioLower, hAmplitudePos] with n hRatioN hAmplitudeN
    exact le_of_lt ((lt_div_iff₀ hAmplitudeN).1 hRatioN)

  exact
    tendsto_atTop_of_eventually_const_mul_le_cooperative
      hdeltaPos
      hCluster.1.2.1
      hLower

/-- Strictly above half-share, the physical terminal clock of the subordinate
channel diverges. -/
theorem h3TerminalBalanceSubordinateChannelPhysicalClock_tendsto_atTop_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    Tendsto
      (fun n : ℕ =>
        (T - τ n) * h3TerminalBalanceSubordinateChannelAt u (τ n))
      atTop atTop := by
  let kappa : ℝ := 2 * theta - 1
  let delta : ℝ := kappa / 2

  have hkappaPos : 0 < kappa := by
    dsimp only [kappa]
    linarith

  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact div_pos hkappaPos (by norm_num)

  have hdeltaLt : delta < kappa := by
    dsimp only [delta]
    linarith

  have hRatio :
      Tendsto
        (fun n : ℕ =>
          h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
        atTop (𝓝 kappa) := by
    simpa only [kappa] using
      h3TerminalBalanceSubordinateRatio_tendsto_of_shareCluster
        hH3 hClass hAt hCluster

  have hRatioLower :
      ∀ᶠ n : ℕ in atTop,
        delta <
          h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n) :=
    hRatio.eventually (Ioi_mem_nhds hdeltaLt)

  have hAmplitudePos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hCluster.1.2.1.eventually (eventually_gt_atTop (0 : ℝ))

  have hClockLower :
      ∀ᶠ n : ℕ in atTop,
        delta * ((T - τ n) * h3TerminalBalanceAmplitudeAt u (τ n))
          ≤
        (T - τ n) * h3TerminalBalanceSubordinateChannelAt u (τ n) := by
    filter_upwards [hRatioLower, hAmplitudePos] with n hRatioN hAmplitudeN

    have hSubordinateLower :
        delta * h3TerminalBalanceAmplitudeAt u (τ n)
          < h3TerminalBalanceSubordinateChannelAt u (τ n) :=
      (lt_div_iff₀ hAmplitudeN).1 hRatioN

    have hTimeNonneg : 0 ≤ T - τ n :=
      sub_nonneg.mpr (hAt n).2.le

    have hMul :=
      mul_le_mul_of_nonneg_left
        (le_of_lt hSubordinateLower)
        hTimeNonneg

    simpa only [mul_assoc, mul_left_comm, mul_comm] using hMul

  exact
    tendsto_atTop_of_eventually_const_mul_le_cooperative
      hdeltaPos
      hCluster.1.2.2.1
      hClockLower

/-- Strictly above half-share, the subordinate channel normalized by full H³
energy diverges. -/
theorem h3TerminalBalanceSubordinateChannelNormalizedRate_tendsto_atTop_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          velocityH3EnergyAt u (τ n))
      atTop atTop := by
  let kappa : ℝ := 2 * theta - 1
  let delta : ℝ := kappa / 2

  have hkappaPos : 0 < kappa := by
    dsimp only [kappa]
    linarith

  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact div_pos hkappaPos (by norm_num)

  have hdeltaLt : delta < kappa := by
    dsimp only [delta]
    linarith

  have hRatio :
      Tendsto
        (fun n : ℕ =>
          h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
        atTop (𝓝 kappa) := by
    simpa only [kappa] using
      h3TerminalBalanceSubordinateRatio_tendsto_of_shareCluster
        hH3 hClass hAt hCluster

  have hRatioLower :
      ∀ᶠ n : ℕ in atTop,
        delta <
          h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n) :=
    hRatio.eventually (Ioi_mem_nhds hdeltaLt)

  have hAmplitudePos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hCluster.1.2.1.eventually (eventually_gt_atTop (0 : ℝ))

  have hNormalizedLower :
      ∀ᶠ n : ℕ in atTop,
        delta *
            (h3TerminalBalanceAmplitudeAt u (τ n) /
              velocityH3EnergyAt u (τ n))
          ≤
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          velocityH3EnergyAt u (τ n) := by
    filter_upwards [hRatioLower, hAmplitudePos] with n hRatioN hAmplitudeN

    have hSubordinateLower :
        delta * h3TerminalBalanceAmplitudeAt u (τ n)
          < h3TerminalBalanceSubordinateChannelAt u (τ n) :=
      (lt_div_iff₀ hAmplitudeN).1 hRatioN

    have hEnergyPos :
        0 < velocityH3EnergyAt u (τ n) := by
      have hOne := one_le_velocityH3EnergyAt u (τ n)
      linarith

    have hDiv :
        (delta * h3TerminalBalanceAmplitudeAt u (τ n)) /
            velocityH3EnergyAt u (τ n)
          ≤
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
            velocityH3EnergyAt u (τ n) :=
      (div_le_div_iff_of_pos_right hEnergyPos).2
        (le_of_lt hSubordinateLower)

    simpa only [mul_div_assoc] using hDiv

  exact
    tendsto_atTop_of_eventually_const_mul_le_cooperative
      hdeltaPos
      hCluster.1.2.2.2.1
      hNormalizedLower

/-- Above half-share, the negative H³ energy derivative diverges because it is
pointwise at least the subordinate channel. -/
theorem negativeVelocityH3EnergyDerivative_tendsto_atTop_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    Tendsto
      (fun n : ℕ => - deriv (velocityH3EnergyAt u) (τ n))
      atTop atTop := by
  have hSubTop :=
    h3TerminalBalanceSubordinateChannelAt_tendsto_atTop_of_half_lt_shareCluster
      hH3 hClass hAt hCluster hTheta

  have hLower :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalBalanceSubordinateChannelAt u (τ n)
          ≤ - deriv (velocityH3EnergyAt u) (τ n) :=
    Eventually.of_forall
      (fun n => by
        unfold h3TerminalBalanceSubordinateChannelAt
        exact min_le_left _ _)

  exact tendsto_atTop_of_eventually_le_cooperative hSubTop hLower

/-- Above half-share, the negative H³ transport derivative diverges because it
is pointwise at least the subordinate channel. -/
theorem negativeVelocityH3TransportDerivative_tendsto_atTop_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    Tendsto
      (fun n : ℕ => - velocityH3TransportDerivativeAt u (τ n))
      atTop atTop := by
  have hSubTop :=
    h3TerminalBalanceSubordinateChannelAt_tendsto_atTop_of_half_lt_shareCluster
      hH3 hClass hAt hCluster hTheta

  have hLower :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalBalanceSubordinateChannelAt u (τ n)
          ≤ - velocityH3TransportDerivativeAt u (τ n) :=
    Eventually.of_forall
      (fun n => by
        unfold h3TerminalBalanceSubordinateChannelAt
        exact min_le_right _ _)

  exact tendsto_atTop_of_eventually_le_cooperative hSubTop hLower

/-- Above half-share, the physical clock of the negative H³ energy derivative
diverges. -/
theorem negativeVelocityH3EnergyDerivativePhysicalClock_tendsto_atTop_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    Tendsto
      (fun n : ℕ =>
        (T - τ n) * (- deriv (velocityH3EnergyAt u) (τ n)))
      atTop atTop := by
  have hSubClock :=
    h3TerminalBalanceSubordinateChannelPhysicalClock_tendsto_atTop_of_half_lt_shareCluster
      hH3 hClass hAt hCluster hTheta

  have hLower :
      ∀ᶠ n : ℕ in atTop,
        (T - τ n) * h3TerminalBalanceSubordinateChannelAt u (τ n)
          ≤
        (T - τ n) * (- deriv (velocityH3EnergyAt u) (τ n)) :=
    Eventually.of_forall
      (fun n => by
        have hSub :
            h3TerminalBalanceSubordinateChannelAt u (τ n)
              ≤ - deriv (velocityH3EnergyAt u) (τ n) := by
          unfold h3TerminalBalanceSubordinateChannelAt
          exact min_le_left _ _
        exact
          mul_le_mul_of_nonneg_left
            hSub
            (sub_nonneg.mpr (hAt n).2.le))

  exact tendsto_atTop_of_eventually_le_cooperative hSubClock hLower

/-- Above half-share, the physical clock of the negative H³ transport derivative
diverges. -/
theorem negativeVelocityH3TransportDerivativePhysicalClock_tendsto_atTop_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    Tendsto
      (fun n : ℕ =>
        (T - τ n) * (- velocityH3TransportDerivativeAt u (τ n)))
      atTop atTop := by
  have hSubClock :=
    h3TerminalBalanceSubordinateChannelPhysicalClock_tendsto_atTop_of_half_lt_shareCluster
      hH3 hClass hAt hCluster hTheta

  have hLower :
      ∀ᶠ n : ℕ in atTop,
        (T - τ n) * h3TerminalBalanceSubordinateChannelAt u (τ n)
          ≤
        (T - τ n) * (- velocityH3TransportDerivativeAt u (τ n)) :=
    Eventually.of_forall
      (fun n => by
        have hSub :
            h3TerminalBalanceSubordinateChannelAt u (τ n)
              ≤ - velocityH3TransportDerivativeAt u (τ n) := by
          unfold h3TerminalBalanceSubordinateChannelAt
          exact min_le_right _ _
        exact
          mul_le_mul_of_nonneg_left
            hSub
            (sub_nonneg.mpr (hAt n).2.le))

  exact tendsto_atTop_of_eventually_le_cooperative hSubClock hLower

/-- Above half-share, the negative H³ energy derivative normalized by H³ energy
diverges. -/
theorem negativeVelocityH3EnergyDerivativeNormalizedRate_tendsto_atTop_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    Tendsto
      (fun n : ℕ =>
        (- deriv (velocityH3EnergyAt u) (τ n)) /
          velocityH3EnergyAt u (τ n))
      atTop atTop := by
  have hSubNormalized :=
    h3TerminalBalanceSubordinateChannelNormalizedRate_tendsto_atTop_of_half_lt_shareCluster
      hH3 hClass hAt hCluster hTheta

  have hLower :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
            velocityH3EnergyAt u (τ n)
          ≤
        (- deriv (velocityH3EnergyAt u) (τ n)) /
            velocityH3EnergyAt u (τ n) :=
    Eventually.of_forall
      (fun n => by
        have hEnergyPos : 0 < velocityH3EnergyAt u (τ n) := by
          have hOne := one_le_velocityH3EnergyAt u (τ n)
          linarith
        have hSub :
            h3TerminalBalanceSubordinateChannelAt u (τ n)
              ≤ - deriv (velocityH3EnergyAt u) (τ n) := by
          unfold h3TerminalBalanceSubordinateChannelAt
          exact min_le_left _ _
        exact (div_le_div_iff_of_pos_right hEnergyPos).2 hSub)

  exact tendsto_atTop_of_eventually_le_cooperative hSubNormalized hLower

/-- Above half-share, the negative H³ transport derivative normalized by H³
energy diverges. -/
theorem negativeVelocityH3TransportDerivativeNormalizedRate_tendsto_atTop_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    Tendsto
      (fun n : ℕ =>
        (- velocityH3TransportDerivativeAt u (τ n)) /
          velocityH3EnergyAt u (τ n))
      atTop atTop := by
  have hSubNormalized :=
    h3TerminalBalanceSubordinateChannelNormalizedRate_tendsto_atTop_of_half_lt_shareCluster
      hH3 hClass hAt hCluster hTheta

  have hLower :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
            velocityH3EnergyAt u (τ n)
          ≤
        (- velocityH3TransportDerivativeAt u (τ n)) /
            velocityH3EnergyAt u (τ n) :=
    Eventually.of_forall
      (fun n => by
        have hEnergyPos : 0 < velocityH3EnergyAt u (τ n) := by
          have hOne := one_le_velocityH3EnergyAt u (τ n)
          linarith
        have hSub :
            h3TerminalBalanceSubordinateChannelAt u (τ n)
              ≤ - velocityH3TransportDerivativeAt u (τ n) := by
          unfold h3TerminalBalanceSubordinateChannelAt
          exact min_le_right _ _
        exact (div_le_div_iff_of_pos_right hEnergyPos).2 hSub)

  exact tendsto_atTop_of_eventually_le_cooperative hSubNormalized hLower

/-- Strictly above half-share, both signed balance channels carry the complete
cooperative raw/clock/normalized divergence cascade on the original sequence. -/
theorem h3TerminalBalanceCooperativeClockCascadeAlong_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    H3TerminalBalanceCooperativeClockCascadeAlong u T τ := by
  exact
    ⟨
      h3TerminalBalanceSubordinateChannelAt_tendsto_atTop_of_half_lt_shareCluster
        hH3 hClass hAt hCluster hTheta,
      h3TerminalBalanceSubordinateChannelPhysicalClock_tendsto_atTop_of_half_lt_shareCluster
        hH3 hClass hAt hCluster hTheta,
      h3TerminalBalanceSubordinateChannelNormalizedRate_tendsto_atTop_of_half_lt_shareCluster
        hH3 hClass hAt hCluster hTheta,
      negativeVelocityH3EnergyDerivative_tendsto_atTop_of_half_lt_shareCluster
        hH3 hClass hAt hCluster hTheta,
      negativeVelocityH3EnergyDerivativePhysicalClock_tendsto_atTop_of_half_lt_shareCluster
        hH3 hClass hAt hCluster hTheta,
      negativeVelocityH3EnergyDerivativeNormalizedRate_tendsto_atTop_of_half_lt_shareCluster
        hH3 hClass hAt hCluster hTheta,
      negativeVelocityH3TransportDerivative_tendsto_atTop_of_half_lt_shareCluster
        hH3 hClass hAt hCluster hTheta,
      negativeVelocityH3TransportDerivativePhysicalClock_tendsto_atTop_of_half_lt_shareCluster
        hH3 hClass hAt hCluster hTheta,
      negativeVelocityH3TransportDerivativeNormalizedRate_tendsto_atTop_of_half_lt_shareCluster
        hH3 hClass hAt hCluster hTheta
    ⟩

/-- Quantitative three-regime classification of every balance-share cluster. -/
theorem h3TerminalBalanceShareCluster_clockCascade_trichotomy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta) :
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
    ) := by
  rcases lt_trichotomy theta ((1 : ℝ) / 2) with hlt | heq | hgt
  · exact
      Or.inl
        ⟨
          hlt,
          h3TerminalBalanceCancellationClockCascadeAlong_of_shareCluster_lt_half
            hH3 hClass hAt hCluster hlt
        ⟩
  · exact
      Or.inr
        (Or.inl
          ⟨
            heq,
            h3TerminalBalanceSubordinateRatio_tendsto_zero_of_shareCluster_eq_half
              hH3 hClass hAt hCluster heq
          ⟩)
  · exact
      Or.inr
        (Or.inr
          ⟨
            hgt,
            h3TerminalBalanceCooperativeClockCascadeAlong_of_half_lt_shareCluster
              hH3 hClass hAt hCluster hgt
          ⟩)

end

end Euclidean
end Bridge
end PrimeTensor
