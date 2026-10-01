import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Cancellation.Orientation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.BKM.Frequency.Linear.Lower.Bound

/-!
# BKM synchronization on the cancellation share cluster

When the balance-share cluster lies below one half, the preceding orientation
extraction freezes one of two cancellation mechanisms on a cofinal subsequence.
If the energy derivative is positive there, the existing terminal BKM estimate
applies pointwise once the same subsequence enters its terminal tail.  Thus no
new time extraction is required: the balance-share parameter, intrinsic cascade,
and BKM vorticity-envelope forcing remain synchronized on one witness.

The alternative orientation, with positive transport derivative, is retained
without forcing it through the positive-energy-growth BKM theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Denominator in the terminal linear characteristic-frequency lower bound
against a vorticity envelope. -/
def h3TerminalBalanceBKMLinearDenominator
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b : ℝ) : ℝ :=
  (
    (4 + 3 * velocityH3Energy0At u b)
      * 4422
      *
        (h3BKMCanonicalSelectedLogGradientConstant
            (Real.sqrt (velocityH3Energy0At u b))
          + 1)
  )
    *
  (
    (4 + 3 * velocityH3Energy0At u b)
        * (velocityH3Energy0At u b + 1)
      + 7
  )

/-- Any terminal share-cluster sequence that has eventually positive H³ energy
derivative inherits the terminal linear BKM frequency-to-vorticity-envelope
lower bound on that same sequence. -/
theorem eventually_balanceShareCluster_characteristicFrequency_linear_lt_vorticityEnvelope_of_positiveGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b theta : ℝ}
    {τ : ℕ → ℝ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VorticityEnvelope u g s)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hGrowth :
      ∀ᶠ n : ℕ in atTop,
        0 < deriv (velocityH3EnergyAt u) (τ n)) :
    ∀ᶠ n : ℕ in atTop,
      (2 * h3TopCharacteristicFrequencyAt u (τ n)) /
          h3TerminalBalanceBKMLinearDenominator u b
        <
      1 + |g (τ n)| := by
  obtain ⟨c, hc, hLower⟩ :=
    exists_terminalTail_positiveGrowth_characteristicFrequency_linear_lt_vorticityEnvelope_of_noH3PathExtension
      hH3 hNoExtension hClass hb hg

  have hPastC :
      ∀ᶠ n : ℕ in atTop,
        c < τ n :=
    hCluster.1.1.eventually (Ioi_mem_nhds hc.2)

  filter_upwards [hPastC, hGrowth] with n hcn hgn
  have hInTail : τ n ∈ Set.Ioo c T :=
    ⟨hcn, (hAt n).2⟩
  simpa [h3TerminalBalanceBKMLinearDenominator] using
    hLower (τ n) hInTail hgn

/-- Below the half-share threshold, freeze the cancellation orientation.  In
the positive-energy-growth orientation, synchronize the linear BKM
frequency-to-vorticity-envelope forcing with the same share-cluster witness;
the positive-transport orientation remains as the neutral alternative. -/
theorem exists_fixed_balanceCancellationOrientation_bkmSubsequence_of_shareCluster_lt_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b theta : ℝ}
    {τ : ℕ → ℝ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VorticityEnvelope u g s)
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
          (∀ᶠ n : ℕ in atTop,
            0 < deriv (velocityH3EnergyAt u) (τ (k n)))
            ∧
          ∀ᶠ n : ℕ in atTop,
            (2 * h3TopCharacteristicFrequencyAt u (τ (k n))) /
                h3TerminalBalanceBKMLinearDenominator u b
              <
            1 + |g (τ (k n))|
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
  obtain ⟨k, hKMono, hClusterSub, hOrientation⟩ :=
    exists_fixed_balanceCancellationOrientation_subsequence_of_shareCluster_lt_half
      hH3 hNoExtension hClass hAt hCluster hTheta

  have hAtSub :
      ∀ n : ℕ,
        τ (k n) ∈ Set.Ioo a T :=
    fun n => hAt (k n)

  rcases hOrientation with hGrowth | hTransport
  · rcases hGrowth with ⟨hIdentities, hGrowthPositive⟩
    have hBKM :
        ∀ᶠ n : ℕ in atTop,
          (2 * h3TopCharacteristicFrequencyAt u (τ (k n))) /
              h3TerminalBalanceBKMLinearDenominator u b
            <
          1 + |g (τ (k n))| :=
      eventually_balanceShareCluster_characteristicFrequency_linear_lt_vorticityEnvelope_of_positiveGrowth
        hH3 hNoExtension hClass hb hg hAtSub hClusterSub hGrowthPositive
    exact
      ⟨
        k,
        hKMono,
        hClusterSub,
        Or.inl ⟨hIdentities, hGrowthPositive, hBKM⟩
      ⟩

  · exact
      ⟨
        k,
        hKMono,
        hClusterSub,
        Or.inr hTransport
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor
