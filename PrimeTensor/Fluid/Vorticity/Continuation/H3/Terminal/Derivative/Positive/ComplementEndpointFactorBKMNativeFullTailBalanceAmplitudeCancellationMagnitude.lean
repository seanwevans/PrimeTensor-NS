import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCancellationActualVorticity

/-!
# Quantitative cancellation magnitude on the balance-share cluster

Below the half-share threshold, the subordinate signed balance channel is
negative.  Its opposite

`C = -S`

is the cancellation magnitude.  The exact subordinate-share limit gives

`C / B -> 1 - 2 * theta`.

Since `theta < 1/2`, this limiting fraction is strictly positive.  The canonical
balance amplitude already diverges on the same share-cluster sequence, so the
cancellation magnitude itself diverges there.

After the cancellation orientation has been frozen, this produces a quantitative
upgrade of the two neutral alternatives:

* decay subordinate: the positive H³ energy derivative tends to `+∞`;
* transport subordinate: the positive H³ transport derivative tends to `+∞`.

The first alternative retains the minimal-envelope and actual-vorticity
divergence proved previously.  No transport-side BKM claim is added to the
second alternative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Magnitude of the opposite-sign subordinate balance channel. -/
def h3TerminalBalanceCancellationMagnitudeAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  - h3TerminalBalanceSubordinateChannelAt u t

/-- The normalized cancellation magnitude converges to `1 - 2 * theta` on any
balance-share cluster. -/
theorem h3TerminalBalanceCancellationMagnitude_div_amplitude_tendsto_of_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
          h3TerminalBalanceAmplitudeAt u (τ n))
      atTop
      (𝓝 (1 - 2 * theta)) := by
  have hSubordinate :=
    h3TerminalBalanceSubordinateRatio_tendsto_of_shareCluster
      hH3 hClass hAt hCluster

  have hNegative := hSubordinate.neg

  have hLimitEq :
      -(2 * theta - 1) = 1 - 2 * theta := by
    ring

  rw [← hLimitEq]
  simpa only [h3TerminalBalanceCancellationMagnitudeAt, neg_div] using hNegative

/-- Below the half-share threshold, the cancellation magnitude diverges on the
same share-cluster sequence as the canonical balance amplitude. -/
theorem h3TerminalBalanceCancellationMagnitudeAt_tendsto_atTop_of_shareCluster_lt_half
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
        h3TerminalBalanceCancellationMagnitudeAt u (τ n))
      atTop atTop := by
  let κ : ℝ := 1 - 2 * theta
  let δ : ℝ := κ / 2

  have hκPos : 0 < κ := by
    dsimp only [κ]
    linarith

  have hδPos : 0 < δ := by
    dsimp only [δ]
    exact div_pos hκPos (by norm_num)

  have hδLtκ : δ < κ := by
    dsimp only [δ]
    linarith

  have hRatio :
      Tendsto
        (fun n : ℕ =>
          h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
        atTop
        (𝓝 κ) := by
    simpa only [κ] using
      h3TerminalBalanceCancellationMagnitude_div_amplitude_tendsto_of_shareCluster
        hH3 hClass hAt hCluster

  have hRatioLower :
      ∀ᶠ n : ℕ in atTop,
        δ <
          h3TerminalBalanceCancellationMagnitudeAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n) :=
    hRatio.eventually (Ioi_mem_nhds hδLtκ)

  have hAmplitudeTop :
      Tendsto
        (fun n : ℕ => h3TerminalBalanceAmplitudeAt u (τ n))
        atTop atTop :=
    hCluster.1.2.1

  have hAmplitudePos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hAmplitudeTop.eventually (eventually_gt_atTop (0 : ℝ))

  refine tendsto_atTop.2 ?_
  intro M

  by_cases hM : M ≤ 0
  · filter_upwards [hRatioLower, hAmplitudePos] with n hRatioN hAmplitudeN

    have hScaled :
        δ * h3TerminalBalanceAmplitudeAt u (τ n)
          < h3TerminalBalanceCancellationMagnitudeAt u (τ n) :=
      (lt_div_iff₀ hAmplitudeN).1 hRatioN

    have hPositive :
        0 < h3TerminalBalanceCancellationMagnitudeAt u (τ n) := by
      have hProductPos :
          0 < δ * h3TerminalBalanceAmplitudeAt u (τ n) :=
        mul_pos hδPos hAmplitudeN
      exact lt_trans hProductPos hScaled

    exact le_trans hM (le_of_lt hPositive)

  · have hMPos : 0 < M := lt_of_not_ge hM

    let R : ℝ := M / δ

    have hAmplitudeLower :
        ∀ᶠ n : ℕ in atTop,
          R ≤ h3TerminalBalanceAmplitudeAt u (τ n) :=
      hAmplitudeTop.eventually (eventually_ge_atTop R)

    filter_upwards [hRatioLower, hAmplitudeLower] with n hRatioN hAmplitudeN

    have hRPos : 0 < R := by
      dsimp only [R]
      exact div_pos hMPos hδPos

    have hAmplitudeNPos :
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
      lt_of_lt_of_le hRPos hAmplitudeN

    have hScaled :
        δ * h3TerminalBalanceAmplitudeAt u (τ n)
          < h3TerminalBalanceCancellationMagnitudeAt u (τ n) :=
      (lt_div_iff₀ hAmplitudeNPos).1 hRatioN

    have hMLe :
        M ≤ h3TerminalBalanceAmplitudeAt u (τ n) * δ := by
      dsimp only [R] at hAmplitudeN
      exact (div_le_iff₀ hδPos).1 hAmplitudeN

    have hMLe' :
        M ≤ δ * h3TerminalBalanceAmplitudeAt u (τ n) := by
      simpa only [mul_comm] using hMLe

    exact le_trans hMLe' (le_of_lt hScaled)

/-- In the decay-subordinate cancellation orientation, the positive H³ energy
derivative diverges on the same share-cluster sequence. -/
theorem velocityH3EnergyDerivative_tendsto_atTop_of_decaySubordinate_shareCluster_lt_half
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
      (fun n : ℕ => deriv (velocityH3EnergyAt u) (τ n))
      atTop atTop := by
  have hCancellation :=
    h3TerminalBalanceCancellationMagnitudeAt_tendsto_atTop_of_shareCluster_lt_half
      hH3 hClass hAt hCluster hTheta

  have hEq :
      (fun n : ℕ =>
        h3TerminalBalanceCancellationMagnitudeAt u (τ n))
        =
      (fun n : ℕ => deriv (velocityH3EnergyAt u) (τ n)) := by
    funext n
    unfold h3TerminalBalanceCancellationMagnitudeAt
    rw [hDecaySubordinate n]
    ring

  rw [hEq] at hCancellation
  exact hCancellation

/-- In the transport-subordinate cancellation orientation, the positive H³
transport derivative diverges on the same share-cluster sequence. -/
theorem velocityH3TransportDerivative_tendsto_atTop_of_transportSubordinate_shareCluster_lt_half
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
      (fun n : ℕ => velocityH3TransportDerivativeAt u (τ n))
      atTop atTop := by
  have hCancellation :=
    h3TerminalBalanceCancellationMagnitudeAt_tendsto_atTop_of_shareCluster_lt_half
      hH3 hClass hAt hCluster hTheta

  have hEq :
      (fun n : ℕ =>
        h3TerminalBalanceCancellationMagnitudeAt u (τ n))
        =
      (fun n : ℕ => velocityH3TransportDerivativeAt u (τ n)) := by
    funext n
    unfold h3TerminalBalanceCancellationMagnitudeAt
    rw [hTransportSubordinate n]
    ring

  rw [hEq] at hCancellation
  exact hCancellation

/-- Below the half-share threshold, the frozen cancellation orientation is
quantitatively divergent.  The growth orientation retains the synchronized
minimal-envelope and actual-vorticity divergence; the transport orientation
carries a divergent positive transport derivative on the same `theta` witness. -/
theorem exists_fixed_balanceCancellationOrientation_divergenceActualVorticitySubsequence_of_shareCluster_lt_half
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
        )
      ) := by
  obtain ⟨k, hKMono, hClusterSub, hOrientation⟩ :=
    exists_fixed_balanceCancellationOrientation_actualVorticitySubsequence_of_shareCluster_lt_half
      hH3 hNoExtension hClass hb hAt hCluster hTheta

  have hAtSub :
      ∀ n : ℕ,
        τ (k n) ∈ Set.Ioo a T :=
    fun n => hAt (k n)

  rcases hOrientation with hGrowth | hTransport
  · rcases hGrowth with
      ⟨hIdentities, _hGrowthPositive, hEnvelope, y, hActual⟩

    have hDerivativeTop :
        Tendsto
          (fun n : ℕ => deriv (velocityH3EnergyAt u) (τ (k n)))
          atTop atTop :=
      velocityH3EnergyDerivative_tendsto_atTop_of_decaySubordinate_shareCluster_lt_half
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
            hDerivativeTop,
            hEnvelope,
            y,
            hActual
          ⟩
      ⟩

  · rcases hTransport with ⟨hIdentities, _hTransportPositive⟩

    have hTransportTop :
        Tendsto
          (fun n : ℕ => velocityH3TransportDerivativeAt u (τ (k n)))
          atTop atTop :=
      velocityH3TransportDerivative_tendsto_atTop_of_transportSubordinate_shareCluster_lt_half
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
            hTransportTop
          ⟩
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor
