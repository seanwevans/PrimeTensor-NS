import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCriticalSubordinatePhysicalRegime
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCriticalOrientation

/-!
# Joint critical dominant-channel and subordinate-sign regimes

At critical half-share two finite choices remain after the asymptotic geometry is
fixed:

* which signed H³ balance channel realizes the canonical dominant amplitude;
* whether the subordinate channel is negative, zero, or positive.

A nested cofinal extraction freezes both choices simultaneously.  This leaves six
explicit physical regimes.  In the cancellation cases the opposite-sign
physical derivative is identified; in the zero cases one physical derivative
vanishes and the other equals twice full H³ dissipation; in the cooperative
cases both physical derivatives are strictly negative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Critical decay-dominant geometry with a negative subordinate transport
channel. -/
def H3TerminalBalanceCriticalDecayCancellationAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalDecayDominantClockCascadeAlong u T τ
    ∧
  (∀ n : ℕ,
    h3TerminalBalanceSubordinateChannelAt u (τ n) < 0)
    ∧
  (∀ n : ℕ,
    deriv (velocityH3EnergyAt u) (τ n) < 0
      ∧ 0 < velocityH3TransportDerivativeAt u (τ n))

/-- Critical decay-dominant geometry with exact zero subordinate transport. -/
def H3TerminalBalanceCriticalDecayExactAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalDecayDominantClockCascadeAlong u T τ
    ∧
  (∀ n : ℕ,
    h3TerminalBalanceSubordinateChannelAt u (τ n) = 0)
    ∧
  (∀ n : ℕ,
    velocityH3TransportDerivativeAt u (τ n) = 0
      ∧
    - deriv (velocityH3EnergyAt u) (τ n)
        = 2 * velocityH3DissipationAt u (τ n))

/-- Critical decay-dominant geometry with a positive subordinate cooperative
channel. -/
def H3TerminalBalanceCriticalDecayCooperativeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalDecayDominantClockCascadeAlong u T τ
    ∧
  (∀ n : ℕ,
    0 < h3TerminalBalanceSubordinateChannelAt u (τ n))
    ∧
  (∀ n : ℕ,
    deriv (velocityH3EnergyAt u) (τ n) < 0
      ∧ velocityH3TransportDerivativeAt u (τ n) < 0)

/-- Critical transport-dominant geometry with a negative subordinate energy
channel. -/
def H3TerminalBalanceCriticalTransportCancellationAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalTransportDominantClockCascadeAlong u T τ
    ∧
  (∀ n : ℕ,
    h3TerminalBalanceSubordinateChannelAt u (τ n) < 0)
    ∧
  (∀ n : ℕ,
    0 < deriv (velocityH3EnergyAt u) (τ n)
      ∧ velocityH3TransportDerivativeAt u (τ n) < 0)

/-- Critical transport-dominant geometry with exact zero subordinate energy
variation. -/
def H3TerminalBalanceCriticalTransportExactAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalTransportDominantClockCascadeAlong u T τ
    ∧
  (∀ n : ℕ,
    h3TerminalBalanceSubordinateChannelAt u (τ n) = 0)
    ∧
  (∀ n : ℕ,
    deriv (velocityH3EnergyAt u) (τ n) = 0
      ∧
    - velocityH3TransportDerivativeAt u (τ n)
        = 2 * velocityH3DissipationAt u (τ n))

/-- Critical transport-dominant geometry with a positive subordinate
cooperative channel. -/
def H3TerminalBalanceCriticalTransportCooperativeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalTransportDominantClockCascadeAlong u T τ
    ∧
  (∀ n : ℕ,
    0 < h3TerminalBalanceSubordinateChannelAt u (τ n))
    ∧
  (∀ n : ℕ,
    deriv (velocityH3EnergyAt u) (τ n) < 0
      ∧ velocityH3TransportDerivativeAt u (τ n) < 0)

/-- Complete jointly frozen critical physical classification. -/
def H3TerminalBalanceCriticalJointPhysicalRegimeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong u T τ
    ∧
  (
    H3TerminalBalanceCriticalDecayCancellationAlong u T τ
      ∨ H3TerminalBalanceCriticalDecayExactAlong u T τ
      ∨ H3TerminalBalanceCriticalDecayCooperativeAlong u T τ
      ∨ H3TerminalBalanceCriticalTransportCancellationAlong u T τ
      ∨ H3TerminalBalanceCriticalTransportExactAlong u T τ
      ∨ H3TerminalBalanceCriticalTransportCooperativeAlong u T τ
  )

private theorem criticalDecayCancellation_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hDecay : H3TerminalBalanceCriticalDecayDominantClockCascadeAlong u T τ)
    (hNegative : ∀ n : ℕ,
      h3TerminalBalanceSubordinateChannelAt u (τ n) < 0) :
    ∀ n : ℕ,
      deriv (velocityH3EnergyAt u) (τ n) < 0
        ∧ 0 < velocityH3TransportDerivativeAt u (τ n) := by
  intro n
  have hIdentities := hDecay.1 n
  have hBalance :=
    h3TerminalBalanceAmplitude_add_subordinateChannel_eq_two_mul_dissipation
      hH3 hClass (hAt n)
  have hDNonneg := velocityH3DissipationAt_nonneg u (τ n)
  have hBPos :
      0 < h3TerminalBalanceAmplitudeAt u (τ n) := by
    linarith [hBalance, hDNonneg, hNegative n]
  constructor
  · rw [hIdentities.1] at hBPos
    linarith
  · have hn := hNegative n
    rw [hIdentities.2] at hn
    linarith

private theorem criticalTransportCancellation_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTransport : H3TerminalBalanceCriticalTransportDominantClockCascadeAlong u T τ)
    (hNegative : ∀ n : ℕ,
      h3TerminalBalanceSubordinateChannelAt u (τ n) < 0) :
    ∀ n : ℕ,
      0 < deriv (velocityH3EnergyAt u) (τ n)
        ∧ velocityH3TransportDerivativeAt u (τ n) < 0 := by
  intro n
  have hIdentities := hTransport.1 n
  have hBalance :=
    h3TerminalBalanceAmplitude_add_subordinateChannel_eq_two_mul_dissipation
      hH3 hClass (hAt n)
  have hDNonneg := velocityH3DissipationAt_nonneg u (τ n)
  have hBPos :
      0 < h3TerminalBalanceAmplitudeAt u (τ n) := by
    linarith [hBalance, hDNonneg, hNegative n]
  constructor
  · have hn := hNegative n
    rw [hIdentities.2] at hn
    linarith
  · rw [hIdentities.1] at hBPos
    linarith

private theorem criticalDecayExact_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hDecay : H3TerminalBalanceCriticalDecayDominantClockCascadeAlong u T τ)
    (hZero : ∀ n : ℕ,
      h3TerminalBalanceSubordinateChannelAt u (τ n) = 0) :
    ∀ n : ℕ,
      velocityH3TransportDerivativeAt u (τ n) = 0
        ∧
      - deriv (velocityH3EnergyAt u) (τ n)
          = 2 * velocityH3DissipationAt u (τ n) := by
  intro n
  have hIdentities := hDecay.1 n
  have hZeroN := hZero n
  have hBalance :=
    h3TerminalBalanceAmplitude_add_subordinateChannel_eq_two_mul_dissipation
      hH3 hClass (hAt n)
  constructor
  · rw [hIdentities.2] at hZeroN
    linarith
  · rw [hIdentities.1, hZero n] at hBalance
    simpa using hBalance

private theorem criticalTransportExact_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTransport : H3TerminalBalanceCriticalTransportDominantClockCascadeAlong u T τ)
    (hZero : ∀ n : ℕ,
      h3TerminalBalanceSubordinateChannelAt u (τ n) = 0) :
    ∀ n : ℕ,
      deriv (velocityH3EnergyAt u) (τ n) = 0
        ∧
      - velocityH3TransportDerivativeAt u (τ n)
          = 2 * velocityH3DissipationAt u (τ n) := by
  intro n
  have hIdentities := hTransport.1 n
  have hZeroN := hZero n
  have hBalance :=
    h3TerminalBalanceAmplitude_add_subordinateChannel_eq_two_mul_dissipation
      hH3 hClass (hAt n)
  constructor
  · rw [hIdentities.2] at hZeroN
    linarith
  · rw [hIdentities.1, hZero n] at hBalance
    simpa using hBalance

/-- At critical half-share, a cofinal subsequence freezes both the dominant
balance channel and the subordinate sign, leaving exactly one of six physical
regimes while preserving the complete three-scale subordinate frontier. -/
theorem exists_fixed_balanceCriticalJointPhysicalRegime_subsequence_of_shareCluster_eq_half
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
      H3TerminalBalanceCriticalJointPhysicalRegimeAlong
        u T (fun n : ℕ => τ (k n)) := by
  obtain ⟨k, hKMono, hClusterK, hPhysicalK⟩ :=
    exists_fixed_balanceCriticalSubordinatePhysicalRegime_subsequence_of_shareCluster_eq_half
      hH3 hNoExtension hClass hAt hCluster hTheta

  have hAtK :
      ∀ n : ℕ,
        τ (k n) ∈ Set.Ioo a T :=
    fun n => hAt (k n)

  obtain ⟨l, hLMono, hClusterKL, hOrientationKL⟩ :=
    exists_fixed_balanceCriticalDominantOrientation_subsequence_of_shareCluster_eq_half
      hH3 hNoExtension hClass hAtK hClusterK hTheta

  let K : ℕ → ℕ :=
    fun n => k (l n)

  have hKFinalMono : StrictMono K := by
    intro m n hmn
    exact hKMono (hLMono hmn)

  have hClusterFinal :
      H3TerminalBalanceShareClusterAlong
        u T (fun n : ℕ => τ (K n)) theta := by
    simpa only [K] using hClusterKL

  have hAtFinal :
      ∀ n : ℕ,
        τ (K n) ∈ Set.Ioo a T :=
    fun n => hAt (K n)

  have hFrontierFinal :
      H3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong
        u T (fun n : ℕ => τ (K n)) :=
    h3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong_of_shareCluster_eq_half
      hH3 hClass hAtFinal hClusterFinal hTheta

  rcases hPhysicalK.2 with hNegative | hZero | hPositive

  · have hNegativeFinal :
        ∀ n : ℕ,
          h3TerminalBalanceSubordinateChannelAt u (τ (K n)) < 0 := by
      intro n
      simpa only [K] using hNegative.1 (l n)

    rcases hOrientationKL with hDecay | hTransport

    · have hDecayFinal :
          H3TerminalBalanceCriticalDecayDominantClockCascadeAlong
            u T (fun n : ℕ => τ (K n)) := by
        simpa only [K] using hDecay
      have hSigns :=
        criticalDecayCancellation_physical
          hH3 hClass hAtFinal hDecayFinal hNegativeFinal
      refine ⟨K, hKFinalMono, hClusterFinal, hFrontierFinal, ?_⟩
      exact Or.inl ⟨hDecayFinal, hNegativeFinal, hSigns⟩

    · have hTransportFinal :
          H3TerminalBalanceCriticalTransportDominantClockCascadeAlong
            u T (fun n : ℕ => τ (K n)) := by
        simpa only [K] using hTransport
      have hSigns :=
        criticalTransportCancellation_physical
          hH3 hClass hAtFinal hTransportFinal hNegativeFinal
      refine ⟨K, hKFinalMono, hClusterFinal, hFrontierFinal, ?_⟩
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inl ⟨hTransportFinal, hNegativeFinal, hSigns⟩)))

  · have hZeroFinal :
        ∀ n : ℕ,
          h3TerminalBalanceSubordinateChannelAt u (τ (K n)) = 0 := by
      intro n
      simpa only [K] using hZero.1 (l n)

    rcases hOrientationKL with hDecay | hTransport

    · have hDecayFinal :
          H3TerminalBalanceCriticalDecayDominantClockCascadeAlong
            u T (fun n : ℕ => τ (K n)) := by
        simpa only [K] using hDecay
      have hExact :=
        criticalDecayExact_physical
          hH3 hClass hAtFinal hDecayFinal hZeroFinal
      refine ⟨K, hKFinalMono, hClusterFinal, hFrontierFinal, ?_⟩
      exact Or.inr (Or.inl ⟨hDecayFinal, hZeroFinal, hExact⟩)

    · have hTransportFinal :
          H3TerminalBalanceCriticalTransportDominantClockCascadeAlong
            u T (fun n : ℕ => τ (K n)) := by
        simpa only [K] using hTransport
      have hExact :=
        criticalTransportExact_physical
          hH3 hClass hAtFinal hTransportFinal hZeroFinal
      refine ⟨K, hKFinalMono, hClusterFinal, hFrontierFinal, ?_⟩
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inl ⟨hTransportFinal, hZeroFinal, hExact⟩))))

  · have hPositiveFinal :
        ∀ n : ℕ,
          0 < h3TerminalBalanceSubordinateChannelAt u (τ (K n)) := by
      intro n
      simpa only [K] using hPositive.1 (l n)

    have hBothNegative :
        ∀ n : ℕ,
          deriv (velocityH3EnergyAt u) (τ (K n)) < 0
            ∧ velocityH3TransportDerivativeAt u (τ (K n)) < 0 := by
      intro n
      exact
        h3TerminalBalanceCritical_positiveSubordinate_physicalSigns
          (hPositiveFinal n)

    rcases hOrientationKL with hDecay | hTransport

    · have hDecayFinal :
          H3TerminalBalanceCriticalDecayDominantClockCascadeAlong
            u T (fun n : ℕ => τ (K n)) := by
        simpa only [K] using hDecay
      refine ⟨K, hKFinalMono, hClusterFinal, hFrontierFinal, ?_⟩
      exact
        Or.inr
          (Or.inr
            (Or.inl ⟨hDecayFinal, hPositiveFinal, hBothNegative⟩))

    · have hTransportFinal :
          H3TerminalBalanceCriticalTransportDominantClockCascadeAlong
            u T (fun n : ℕ => τ (K n)) := by
        simpa only [K] using hTransport
      refine ⟨K, hKFinalMono, hClusterFinal, hFrontierFinal, ?_⟩
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  ⟨hTransportFinal, hPositiveFinal, hBothNegative⟩))))

end

end Euclidean
end Bridge
end PrimeTensor
