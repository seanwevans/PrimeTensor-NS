import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeSubordinateCluster

/-!
# Cancellation orientation for the balance-amplitude share cluster

When the asymptotic dissipation share satisfies `theta < 1/2`, the normalized
subordinate balance channel has a strictly negative limit.  Thus the two signed
balance channels eventually have opposite signs.

This file freezes which channel is subordinate on a cofinal subsequence while
preserving the same balance-share cluster parameter `theta` and the full
amplitude/intrinsic cascade.

There are exactly two neutral possibilities:

* decay subordinate: `-E'` is the minimum, so `E' > 0` eventually and adverse
  transport is the dominant canonical amplitude;
* transport subordinate: `-Transport` is the minimum, so the transport
  derivative is positive eventually and decay is the dominant canonical
  amplitude.

No preference between the two mechanisms is imposed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A negative subordinate channel fixes one of the two cancellation
orientations pointwise. -/
theorem h3TerminalBalanceCancellation_orientation_of_subordinate_negative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hNegative : h3TerminalBalanceSubordinateChannelAt u t < 0) :
    (
      h3TerminalBalanceSubordinateChannelAt u t
          = - deriv (velocityH3EnergyAt u) t
        ∧
      h3TerminalBalanceAmplitudeAt u t
          = - velocityH3TransportDerivativeAt u t
        ∧
      0 < deriv (velocityH3EnergyAt u) t
    )
      ∨
    (
      h3TerminalBalanceSubordinateChannelAt u t
          = - velocityH3TransportDerivativeAt u t
        ∧
      h3TerminalBalanceAmplitudeAt u t
          = - deriv (velocityH3EnergyAt u) t
        ∧
      0 < velocityH3TransportDerivativeAt u t
    ) := by
  rcases
    le_total
      (- deriv (velocityH3EnergyAt u) t)
      (- velocityH3TransportDerivativeAt u t)
    with hDecayLeTransport | hTransportLeDecay

  · left
    have hSubordinate :
        h3TerminalBalanceSubordinateChannelAt u t
          = - deriv (velocityH3EnergyAt u) t := by
      unfold h3TerminalBalanceSubordinateChannelAt
      exact min_eq_left hDecayLeTransport

    have hAmplitude :
        h3TerminalBalanceAmplitudeAt u t
          = - velocityH3TransportDerivativeAt u t := by
      rw [h3TerminalBalanceAmplitudeAt]
      exact max_eq_right hDecayLeTransport

    have hGrowth :
        0 < deriv (velocityH3EnergyAt u) t := by
      rw [hSubordinate] at hNegative
      linarith

    exact ⟨hSubordinate, hAmplitude, hGrowth⟩

  · right
    have hSubordinate :
        h3TerminalBalanceSubordinateChannelAt u t
          = - velocityH3TransportDerivativeAt u t := by
      unfold h3TerminalBalanceSubordinateChannelAt
      exact min_eq_right hTransportLeDecay

    have hAmplitude :
        h3TerminalBalanceAmplitudeAt u t
          = - deriv (velocityH3EnergyAt u) t := by
      rw [h3TerminalBalanceAmplitudeAt]
      exact max_eq_left hTransportLeDecay

    have hTransportPositive :
        0 < velocityH3TransportDerivativeAt u t := by
      rw [hSubordinate] at hNegative
      linarith

    exact ⟨hSubordinate, hAmplitude, hTransportPositive⟩

/-- If `theta < 1/2`, a cofinal subsequence freezes one cancellation orientation
while retaining the same share cluster and full terminal cascade. -/
theorem exists_fixed_balanceCancellationOrientation_subsequence_of_shareCluster_lt_half
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
          ∀ᶠ n : ℕ in atTop,
            0 < deriv (velocityH3EnergyAt u) (τ (k n))
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
          ∀ᶠ n : ℕ in atTop,
            0 < velocityH3TransportDerivativeAt u (τ (k n))
        )
      ) := by
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

  have hSubordinateNegative :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalBalanceSubordinateChannelAt u (τ n) < 0 :=
    eventually_h3TerminalBalanceSubordinateChannel_negative_of_shareCluster_lt_half
      hH3 hClass hAt hCluster hTheta

  have hSubordinateNegativeSub :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalBalanceSubordinateChannelAt u (τ (k n)) < 0 :=
    hKTop.eventually hSubordinateNegative

  cases q with
  | false =>
      refine ⟨k, hKMono, hClusterSub, Or.inr ?_⟩

      have hIdentities :
          ∀ n : ℕ,
            h3TerminalBalanceSubordinateChannelAt u (τ (k n))
                = - velocityH3TransportDerivativeAt u (τ (k n))
              ∧
            h3TerminalBalanceAmplitudeAt u (τ (k n))
                = - deriv (velocityH3EnergyAt u) (τ (k n)) := by
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
        · unfold h3TerminalBalanceSubordinateChannelAt
          exact min_eq_right hOrder
        · rw [h3TerminalBalanceAmplitudeAt]
          exact max_eq_left hOrder

      have hTransportPositive :
          ∀ᶠ n : ℕ in atTop,
            0 < velocityH3TransportDerivativeAt u (τ (k n)) := by
        filter_upwards [hSubordinateNegativeSub] with n hn
        have hEq := (hIdentities n).1
        rw [hEq] at hn
        linarith

      exact ⟨hIdentities, hTransportPositive⟩

  | true =>
      refine ⟨k, hKMono, hClusterSub, Or.inl ?_⟩

      have hIdentities :
          ∀ n : ℕ,
            h3TerminalBalanceSubordinateChannelAt u (τ (k n))
                = - deriv (velocityH3EnergyAt u) (τ (k n))
              ∧
            h3TerminalBalanceAmplitudeAt u (τ (k n))
                = - velocityH3TransportDerivativeAt u (τ (k n)) := by
        intro n
        have hOrder :
            (- deriv (velocityH3EnergyAt u) (τ (k n)))
              ≤ (- velocityH3TransportDerivativeAt u (τ (k n))) := by
          have hFixed := hChannelFixed n
          simpa [channel] using hFixed

        constructor
        · unfold h3TerminalBalanceSubordinateChannelAt
          exact min_eq_left hOrder
        · rw [h3TerminalBalanceAmplitudeAt]
          exact max_eq_right hOrder

      have hGrowthPositive :
          ∀ᶠ n : ℕ in atTop,
            0 < deriv (velocityH3EnergyAt u) (τ (k n)) := by
        filter_upwards [hSubordinateNegativeSub] with n hn
        have hEq := (hIdentities n).1
        rw [hEq] at hn
        linarith

      exact ⟨hIdentities, hGrowthPositive⟩

end

end Euclidean
end Bridge
end PrimeTensor
