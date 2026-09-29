import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCancellationMagnitude

/-!
# Physical-clock and normalized cancellation rates on the balance-share cluster

If the asymptotic dissipation share satisfies `theta < 1/2`, the cancellation
magnitude `C = -S` occupies a fixed positive fraction of the canonical balance
amplitude `B`:

`C / B -> 1 - 2 * theta > 0`.

The share cluster already carries

* `B -> +∞`,
* `(T-t) B -> +∞`, and
* `B / E -> +∞`.

Therefore the cancellation magnitude inherits the same three divergence modes.
After the cancellation orientation is frozen, these become corresponding raw,
physical-clock, and energy-normalized divergence statements for either the
positive H³-energy derivative or the positive H³-transport derivative.

The positive-energy-growth orientation retains the synchronized minimal-envelope
and actual-vorticity divergence.  No BKM conclusion is imposed on the
positive-transport orientation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem tendsto_atTop_of_eventually_const_mul_le
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

/-- Below the half-share threshold, the physical terminal clock of the
cancellation magnitude diverges on the same balance-share sequence. -/
theorem h3TerminalBalanceCancellationMagnitudePhysicalClock_tendsto_atTop_of_shareCluster_lt_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta < (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        (T - τ n) * h3TerminalBalanceCancellationMagnitudeAt u (τ n))
      atTop atTop := by
  let kappa : ℝ := 1 - 2 * theta
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
          h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
        atTop (𝓝 kappa) := by
    simpa only [kappa] using
      h3TerminalBalanceCancellationMagnitude_div_amplitude_tendsto_of_shareCluster
        hH3 hClass hAt hCluster

  have hRatioLower :
      ∀ᶠ n : ℕ in atTop,
        delta <
          h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n) :=
    hRatio.eventually (Ioi_mem_nhds hdeltaLt)

  have hAmplitudePos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hCluster.1.2.1.eventually (eventually_gt_atTop (0 : ℝ))

  have hClockLower :
      ∀ᶠ n : ℕ in atTop,
        delta *
            ((T - τ n) * h3TerminalBalanceAmplitudeAt u (τ n))
          ≤
        (T - τ n) * h3TerminalBalanceCancellationMagnitudeAt u (τ n) := by
    filter_upwards [hRatioLower, hAmplitudePos] with n hRatioN hAmplitudeN

    have hCancellationLower :
        delta * h3TerminalBalanceAmplitudeAt u (τ n)
          < h3TerminalBalanceCancellationMagnitudeAt u (τ n) :=
      (lt_div_iff₀ hAmplitudeN).1 hRatioN

    have hTimePos : 0 < T - τ n :=
      sub_pos.mpr (hAt n).2

    have hMul :=
      mul_le_mul_of_nonneg_left
        (le_of_lt hCancellationLower)
        (le_of_lt hTimePos)

    simpa only [mul_assoc, mul_left_comm, mul_comm] using hMul

  exact
    tendsto_atTop_of_eventually_const_mul_le
      hdeltaPos
      hCluster.1.2.2.1
      hClockLower

/-- Below the half-share threshold, the cancellation magnitude normalized by
full H³ energy diverges on the same balance-share sequence. -/
theorem h3TerminalBalanceCancellationMagnitudeNormalizedRate_tendsto_atTop_of_shareCluster_lt_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta < (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
          velocityH3EnergyAt u (τ n))
      atTop atTop := by
  let kappa : ℝ := 1 - 2 * theta
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
          h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
        atTop (𝓝 kappa) := by
    simpa only [kappa] using
      h3TerminalBalanceCancellationMagnitude_div_amplitude_tendsto_of_shareCluster
        hH3 hClass hAt hCluster

  have hRatioLower :
      ∀ᶠ n : ℕ in atTop,
        delta <
          h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
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
        h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
          velocityH3EnergyAt u (τ n) := by
    filter_upwards [hRatioLower, hAmplitudePos] with n hRatioN hAmplitudeN

    have hCancellationLower :
        delta * h3TerminalBalanceAmplitudeAt u (τ n)
          < h3TerminalBalanceCancellationMagnitudeAt u (τ n) :=
      (lt_div_iff₀ hAmplitudeN).1 hRatioN

    have hEnergyPos :
        0 < velocityH3EnergyAt u (τ n) := by
      have hOne := one_le_velocityH3EnergyAt u (τ n)
      linarith

    have hDiv :
        (delta * h3TerminalBalanceAmplitudeAt u (τ n)) /
            velocityH3EnergyAt u (τ n)
          ≤
        h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
            velocityH3EnergyAt u (τ n) :=
      (div_le_div_iff_of_pos_right hEnergyPos).2
        (le_of_lt hCancellationLower)

    simpa only [mul_div_assoc] using hDiv

  exact
    tendsto_atTop_of_eventually_const_mul_le
      hdeltaPos
      hCluster.1.2.2.2.1
      hNormalizedLower

/-- In the decay-subordinate orientation, the physical clock of the positive H³
energy derivative diverges. -/
theorem velocityH3EnergyDerivativePhysicalClock_tendsto_atTop_of_decaySubordinate_shareCluster_lt_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta < (1 : ℝ) / 2)
    (hDecaySubordinate :
      ∀ n : ℕ,
        h3TerminalBalanceSubordinateChannelAt u (τ n)
          = - deriv (velocityH3EnergyAt u) (τ n)) :
    Tendsto
      (fun n : ℕ =>
        (T - τ n) * deriv (velocityH3EnergyAt u) (τ n))
      atTop atTop := by
  have hClock :=
    h3TerminalBalanceCancellationMagnitudePhysicalClock_tendsto_atTop_of_shareCluster_lt_half
      hH3 hClass hAt hCluster hTheta

  have hEq :
      (fun n : ℕ =>
        (T - τ n) * h3TerminalBalanceCancellationMagnitudeAt u (τ n))
        =
      (fun n : ℕ =>
        (T - τ n) * deriv (velocityH3EnergyAt u) (τ n)) := by
    funext n
    unfold h3TerminalBalanceCancellationMagnitudeAt
    rw [hDecaySubordinate n]
    ring

  rw [hEq] at hClock
  exact hClock

/-- In the decay-subordinate orientation, the positive H³ energy derivative
normalized by H³ energy diverges. -/
theorem velocityH3EnergyDerivativeNormalizedRate_tendsto_atTop_of_decaySubordinate_shareCluster_lt_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta < (1 : ℝ) / 2)
    (hDecaySubordinate :
      ∀ n : ℕ,
        h3TerminalBalanceSubordinateChannelAt u (τ n)
          = - deriv (velocityH3EnergyAt u) (τ n)) :
    Tendsto
      (fun n : ℕ =>
        deriv (velocityH3EnergyAt u) (τ n) /
          velocityH3EnergyAt u (τ n))
      atTop atTop := by
  have hNormalized :=
    h3TerminalBalanceCancellationMagnitudeNormalizedRate_tendsto_atTop_of_shareCluster_lt_half
      hH3 hClass hAt hCluster hTheta

  have hEq :
      (fun n : ℕ =>
        h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
          velocityH3EnergyAt u (τ n))
        =
      (fun n : ℕ =>
        deriv (velocityH3EnergyAt u) (τ n) /
          velocityH3EnergyAt u (τ n)) := by
    funext n
    unfold h3TerminalBalanceCancellationMagnitudeAt
    rw [hDecaySubordinate n]
    ring

  rw [hEq] at hNormalized
  exact hNormalized

/-- In the transport-subordinate orientation, the physical clock of the positive
H³ transport derivative diverges. -/
theorem velocityH3TransportDerivativePhysicalClock_tendsto_atTop_of_transportSubordinate_shareCluster_lt_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta < (1 : ℝ) / 2)
    (hTransportSubordinate :
      ∀ n : ℕ,
        h3TerminalBalanceSubordinateChannelAt u (τ n)
          = - velocityH3TransportDerivativeAt u (τ n)) :
    Tendsto
      (fun n : ℕ =>
        (T - τ n) * velocityH3TransportDerivativeAt u (τ n))
      atTop atTop := by
  have hClock :=
    h3TerminalBalanceCancellationMagnitudePhysicalClock_tendsto_atTop_of_shareCluster_lt_half
      hH3 hClass hAt hCluster hTheta

  have hEq :
      (fun n : ℕ =>
        (T - τ n) * h3TerminalBalanceCancellationMagnitudeAt u (τ n))
        =
      (fun n : ℕ =>
        (T - τ n) * velocityH3TransportDerivativeAt u (τ n)) := by
    funext n
    unfold h3TerminalBalanceCancellationMagnitudeAt
    rw [hTransportSubordinate n]
    ring

  rw [hEq] at hClock
  exact hClock

/-- In the transport-subordinate orientation, the positive H³ transport
derivative normalized by H³ energy diverges. -/
theorem velocityH3TransportDerivativeNormalizedRate_tendsto_atTop_of_transportSubordinate_shareCluster_lt_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta < (1 : ℝ) / 2)
    (hTransportSubordinate :
      ∀ n : ℕ,
        h3TerminalBalanceSubordinateChannelAt u (τ n)
          = - velocityH3TransportDerivativeAt u (τ n)) :
    Tendsto
      (fun n : ℕ =>
        velocityH3TransportDerivativeAt u (τ n) /
          velocityH3EnergyAt u (τ n))
      atTop atTop := by
  have hNormalized :=
    h3TerminalBalanceCancellationMagnitudeNormalizedRate_tendsto_atTop_of_shareCluster_lt_half
      hH3 hClass hAt hCluster hTheta

  have hEq :
      (fun n : ℕ =>
        h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
          velocityH3EnergyAt u (τ n))
        =
      (fun n : ℕ =>
        velocityH3TransportDerivativeAt u (τ n) /
          velocityH3EnergyAt u (τ n)) := by
    funext n
    unfold h3TerminalBalanceCancellationMagnitudeAt
    rw [hTransportSubordinate n]
    ring

  rw [hEq] at hNormalized
  exact hNormalized

/-- Below the half-share threshold, one frozen cancellation orientation carries
raw, physical-clock, and normalized divergence on the same share-cluster
subsequence.  The positive-growth branch also retains minimal-envelope and
actual-vorticity divergence. -/
theorem exists_fixed_balanceCancellationOrientation_clockRatesActualVorticitySubsequence_of_shareCluster_lt_half
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
    (hTheta : theta < (1 : ℝ) / 2) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      H3TerminalBalanceShareClusterAlong
        u T (fun n : ℕ => τ (k n)) theta
        ∧
      (
        (
          (∀ n : ℕ,
            h3TerminalBalanceSubordinateChannelAt u (τ (k n))
                = - deriv (velocityH3EnergyAt u) (τ (k n))
              ∧
            h3TerminalBalanceAmplitudeAt u (τ (k n))
                = - velocityH3TransportDerivativeAt u (τ (k n)))
            ∧
          Tendsto
            (fun n : ℕ => deriv (velocityH3EnergyAt u) (τ (k n)))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              (T - τ (k n)) * deriv (velocityH3EnergyAt u) (τ (k n)))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              deriv (velocityH3EnergyAt u) (τ (k n)) /
                velocityH3EnergyAt u (τ (k n)))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              h3MinimalVorticityEnvelopeAt u (τ (k n)))
            atTop atTop
            ∧
          ∃ y : ℕ → Point3,
            Tendsto
              (fun n : ℕ =>
                h3ActualVorticityMaxAt u (τ (k n)) (y n))
              atTop atTop
        )
          ∨
        (
          (∀ n : ℕ,
            h3TerminalBalanceSubordinateChannelAt u (τ (k n))
                = - velocityH3TransportDerivativeAt u (τ (k n))
              ∧
            h3TerminalBalanceAmplitudeAt u (τ (k n))
                = - deriv (velocityH3EnergyAt u) (τ (k n)))
            ∧
          Tendsto
            (fun n : ℕ => velocityH3TransportDerivativeAt u (τ (k n)))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              (T - τ (k n)) * velocityH3TransportDerivativeAt u (τ (k n)))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              velocityH3TransportDerivativeAt u (τ (k n)) /
                velocityH3EnergyAt u (τ (k n)))
            atTop atTop
        )
      ) := by
  obtain ⟨k, hKMono, hClusterSub, hOrientation⟩ :=
    exists_fixed_balanceCancellationOrientation_divergenceActualVorticitySubsequence_of_shareCluster_lt_half
      hH3 hNoExtension hClass hb hAt hCluster hTheta

  have hAtSub :
      ∀ n : ℕ,
        τ (k n) ∈ Set.Ioo a T :=
    fun n => hAt (k n)

  rcases hOrientation with hGrowth | hTransport
  · rcases hGrowth with
      ⟨hIdentities, hRawTop, hEnvelopeTop, y, hActualTop⟩

    have hClockTop :
        Tendsto
          (fun n : ℕ =>
            (T - τ (k n)) * deriv (velocityH3EnergyAt u) (τ (k n)))
          atTop atTop :=
      velocityH3EnergyDerivativePhysicalClock_tendsto_atTop_of_decaySubordinate_shareCluster_lt_half
        hH3 hClass hAtSub hClusterSub hTheta
        (fun n => (hIdentities n).1)

    have hNormalizedTop :
        Tendsto
          (fun n : ℕ =>
            deriv (velocityH3EnergyAt u) (τ (k n)) /
              velocityH3EnergyAt u (τ (k n)))
          atTop atTop :=
      velocityH3EnergyDerivativeNormalizedRate_tendsto_atTop_of_decaySubordinate_shareCluster_lt_half
        hH3 hClass hAtSub hClusterSub hTheta
        (fun n => (hIdentities n).1)

    exact
      ⟨
        k,
        hKMono,
        hClusterSub,
        Or.inl
          ⟨
            hIdentities,
            hRawTop,
            hClockTop,
            hNormalizedTop,
            hEnvelopeTop,
            y,
            hActualTop
          ⟩
      ⟩

  · rcases hTransport with ⟨hIdentities, hRawTop⟩

    have hClockTop :
        Tendsto
          (fun n : ℕ =>
            (T - τ (k n)) * velocityH3TransportDerivativeAt u (τ (k n)))
          atTop atTop :=
      velocityH3TransportDerivativePhysicalClock_tendsto_atTop_of_transportSubordinate_shareCluster_lt_half
        hH3 hClass hAtSub hClusterSub hTheta
        (fun n => (hIdentities n).1)

    have hNormalizedTop :
        Tendsto
          (fun n : ℕ =>
            velocityH3TransportDerivativeAt u (τ (k n)) /
              velocityH3EnergyAt u (τ (k n)))
          atTop atTop :=
      velocityH3TransportDerivativeNormalizedRate_tendsto_atTop_of_transportSubordinate_shareCluster_lt_half
        hH3 hClass hAtSub hClusterSub hTheta
        (fun n => (hIdentities n).1)

    exact
      ⟨
        k,
        hKMono,
        hClusterSub,
        Or.inr
          ⟨
            hIdentities,
            hRawTop,
            hClockTop,
            hNormalizedTop
          ⟩
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor
