import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeShareCluster

/-!
# Subordinate balance channel from the asymptotic share cluster

Let

* `B` be the canonical balance amplitude, the maximum of negative H³ energy
  derivative and negative H³ transport;
* `S` be the subordinate balance channel, their minimum;
* `D` be full H³ dissipation.

The exact H³ balance gives

`B + S = 2 D`.

Whenever `B > 0`, normalization by the canonical amplitude gives

`S / B = 2 (D / B) - 1`.

Consequently, along any asymptotic balance-share cluster with dissipation share
`theta`, the subordinate normalized channel converges to `2 * theta - 1`.
This gives a branch-free structural interpretation of the share parameter:

* `theta < 1/2`: the subordinate channel is eventually negative, so the two
  signed balance channels are in a cancellation regime;
* `theta = 1/2`: the subordinate channel is asymptotically negligible relative
  to the dominant amplitude;
* `theta > 1/2`: the subordinate channel is eventually positive, so both signed
  balance channels contribute with the same sign.

No choice between decay and transport as the dominant channel is required.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The smaller of the two signed H³ balance channels. -/
def h3TerminalBalanceSubordinateChannelAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  min
    (- deriv (velocityH3EnergyAt u) t)
    (- velocityH3TransportDerivativeAt u t)

/-- The dominant canonical amplitude plus the subordinate channel equals twice
full H³ dissipation. -/
theorem h3TerminalBalanceAmplitude_add_subordinateChannel_eq_two_mul_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalBalanceAmplitudeAt u t
        + h3TerminalBalanceSubordinateChannelAt u t
      =
    2 * velocityH3DissipationAt u t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht

  have hSum :
      (- deriv (velocityH3EnergyAt u) t)
          + (- velocityH3TransportDerivativeAt u t)
        =
      2 * velocityH3DissipationAt u t := by
    linarith

  rcases
    le_total
      (- deriv (velocityH3EnergyAt u) t)
      (- velocityH3TransportDerivativeAt u t)
    with hDecayLeTransport | hTransportLeDecay

  · unfold h3TerminalBalanceSubordinateChannelAt
    rw [h3TerminalBalanceAmplitudeAt]
    rw [max_eq_right hDecayLeTransport, min_eq_left hDecayLeTransport]
    simpa [add_comm] using hSum

  · unfold h3TerminalBalanceSubordinateChannelAt
    rw [h3TerminalBalanceAmplitudeAt]
    rw [max_eq_left hTransportLeDecay, min_eq_right hTransportLeDecay]
    exact hSum

/-- Once the canonical amplitude is positive, the subordinate channel normalized
by `B` is exactly `2` times the dissipation share minus `1`. -/
theorem h3TerminalBalanceSubordinateChannel_div_amplitude_eq_two_mul_dissipationShare_sub_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hBPos : 0 < h3TerminalBalanceAmplitudeAt u t) :
    h3TerminalBalanceSubordinateChannelAt u t /
        h3TerminalBalanceAmplitudeAt u t
      =
    2 * h3TerminalBalanceDissipationShareAt u t - 1 := by
  have hExact :=
    h3TerminalBalanceAmplitude_add_subordinateChannel_eq_two_mul_dissipation
      hH3 hClass ht

  have hBNe :
      h3TerminalBalanceAmplitudeAt u t ≠ 0 :=
    ne_of_gt hBPos

  unfold h3TerminalBalanceDissipationShareAt
  field_simp [hBNe]
  linarith

/-- The asymptotic dissipation share `theta` determines the normalized
subordinate-channel limit exactly as `2 * theta - 1`. -/
theorem h3TerminalBalanceSubordinateRatio_tendsto_of_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          h3TerminalBalanceAmplitudeAt u (τ n))
      atTop
      (𝓝 (2 * theta - 1)) := by
  have hBPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hCluster.1.2.1.eventually
      (eventually_gt_atTop (0 : ℝ))

  have hEq :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n)
          =
        2 * h3TerminalBalanceDissipationShareAt u (τ n) - 1 := by
    filter_upwards [hBPos] with n hn
    exact
      h3TerminalBalanceSubordinateChannel_div_amplitude_eq_two_mul_dissipationShare_sub_one
        hH3 hClass (hAt n) hn

  have hTwice :
      Tendsto
        (fun n : ℕ =>
          (2 : ℝ) * h3TerminalBalanceDissipationShareAt u (τ n))
        atTop
        (𝓝 (2 * theta)) :=
    tendsto_const_nhds.mul hCluster.2.1

  have hAffine :
      Tendsto
        (fun n : ℕ =>
          (2 : ℝ) * h3TerminalBalanceDissipationShareAt u (τ n) - 1)
        atTop
        (𝓝 (2 * theta - 1)) :=
    hTwice.sub tendsto_const_nhds

  have hEq' :
      ∀ᶠ n : ℕ in atTop,
        (2 : ℝ) * h3TerminalBalanceDissipationShareAt u (τ n) - 1
          =
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          h3TerminalBalanceAmplitudeAt u (τ n) := by
    filter_upwards [hEq] with n hn
    exact hn.symm

  exact hAffine.congr' hEq'

/-- If the limiting dissipation share is strictly below one half, the
subordinate signed balance channel is eventually negative. -/
theorem eventually_h3TerminalBalanceSubordinateChannel_negative_of_shareCluster_lt_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta < (1 : ℝ) / 2) :
    ∀ᶠ n : ℕ in atTop,
      h3TerminalBalanceSubordinateChannelAt u (τ n) < 0 := by
  have hLimit :=
    h3TerminalBalanceSubordinateRatio_tendsto_of_shareCluster
      hH3 hClass hAt hCluster

  have hLimitNeg :
      2 * theta - 1 < (0 : ℝ) := by
    linarith

  have hRatioNeg :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n)
          < 0 :=
    hLimit.eventually (Iio_mem_nhds hLimitNeg)

  have hBPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hCluster.1.2.1.eventually
      (eventually_gt_atTop (0 : ℝ))

  filter_upwards [hRatioNeg, hBPos] with n hRatio hnB
  have hScaled :=
    (div_lt_iff₀ hnB).1 hRatio
  simpa using hScaled

/-- If the limiting dissipation share is strictly above one half, the
subordinate signed balance channel is eventually positive. -/
theorem eventually_h3TerminalBalanceSubordinateChannel_positive_of_half_lt_shareCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : (1 : ℝ) / 2 < theta) :
    ∀ᶠ n : ℕ in atTop,
      0 < h3TerminalBalanceSubordinateChannelAt u (τ n) := by
  have hLimit :=
    h3TerminalBalanceSubordinateRatio_tendsto_of_shareCluster
      hH3 hClass hAt hCluster

  have hLimitPos :
      (0 : ℝ) < 2 * theta - 1 := by
    linarith

  have hRatioPos :
      ∀ᶠ n : ℕ in atTop,
        0 <
          h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n) :=
    hLimit.eventually (Ioi_mem_nhds hLimitPos)

  have hBPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hCluster.1.2.1.eventually
      (eventually_gt_atTop (0 : ℝ))

  filter_upwards [hRatioPos, hBPos] with n hRatio hnB
  have hScaled :=
    (lt_div_iff₀ hnB).1 hRatio
  simpa using hScaled

/-- At the critical half-share, the subordinate channel is negligible relative
to the canonical amplitude. -/
theorem h3TerminalBalanceSubordinateRatio_tendsto_zero_of_shareCluster_eq_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          h3TerminalBalanceAmplitudeAt u (τ n))
      atTop
      (𝓝 (0 : ℝ)) := by
  have hLimit :=
    h3TerminalBalanceSubordinateRatio_tendsto_of_shareCluster
      hH3 hClass hAt hCluster
  convert hLimit using 1
  · norm_num [hTheta]

/-- Every asymptotic balance-share cluster falls into exactly one of the three
subordinate-channel sign regimes determined by the position of `theta` relative
to one half. -/
theorem h3TerminalBalanceSubordinateChannel_shareCluster_trichotomy
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
      ∀ᶠ n : ℕ in atTop,
        h3TerminalBalanceSubordinateChannelAt u (τ n) < 0
    )
      ∨
    (
      theta = (1 : ℝ) / 2
        ∧
      Tendsto
        (fun n : ℕ =>
          h3TerminalBalanceSubordinateChannelAt u (τ n) /
            h3TerminalBalanceAmplitudeAt u (τ n))
        atTop
        (𝓝 (0 : ℝ))
    )
      ∨
    (
      (1 : ℝ) / 2 < theta
        ∧
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceSubordinateChannelAt u (τ n)
    ) := by
  rcases lt_trichotomy theta ((1 : ℝ) / 2) with hlt | heq | hgt
  · exact
      Or.inl
        ⟨
          hlt,
          eventually_h3TerminalBalanceSubordinateChannel_negative_of_shareCluster_lt_half
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
            eventually_h3TerminalBalanceSubordinateChannel_positive_of_half_lt_shareCluster
              hH3 hClass hAt hCluster hgt
          ⟩)

end

end Euclidean
end Bridge
end PrimeTensor
