import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Critical.Subordinate.Sign

/-!
# Physical regimes of the critical subordinate sign

The critical subordinate-sign extraction freezes one of the three signs of the
lower-order balance channel `S`.  This file translates those signs into the
corresponding physical H³ balance geometry.

* `S < 0`: the two signed balance channels have opposite signs, giving one of
  the two pointwise cancellation orientations.
* `S = 0`: the canonical amplitude is exactly `2D`, and one signed balance
  channel vanishes exactly.
* `S > 0`: both signed balance channels are positive, hence both the H³ energy
  derivative and the H³ transport derivative are strictly negative.

All statements remain conditional consequences of the critical half-share
witness and make no claim that any one regime must occur for a solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Exact geometry when the critical subordinate channel vanishes.  The
canonical amplitude is then exactly twice full H³ dissipation and one of the
two signed balance channels is identically zero at that time. -/
theorem h3TerminalBalanceCritical_zeroSubordinate_geometry
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hZero : h3TerminalBalanceSubordinateChannelAt u t = 0) :
    h3TerminalBalanceAmplitudeAt u t
        = 2 * velocityH3DissipationAt u t
      ∧
    (
      (deriv (velocityH3EnergyAt u) t = 0
        ∧ h3TerminalBalanceAmplitudeAt u t
            = - velocityH3TransportDerivativeAt u t)
        ∨
      (velocityH3TransportDerivativeAt u t = 0
        ∧ h3TerminalBalanceAmplitudeAt u t
            = - deriv (velocityH3EnergyAt u) t)
    ) := by
  have hBalance :=
    h3TerminalBalanceAmplitude_add_subordinateChannel_eq_two_mul_dissipation
      hH3 hClass ht

  have hAmplitudeExact :
      h3TerminalBalanceAmplitudeAt u t
        = 2 * velocityH3DissipationAt u t := by
    rw [hZero] at hBalance
    simpa using hBalance

  let X : ℝ := - deriv (velocityH3EnergyAt u) t
  let Y : ℝ := - velocityH3TransportDerivativeAt u t

  have hMin : min X Y = 0 := by
    simpa only [X, Y, h3TerminalBalanceSubordinateChannelAt] using hZero

  rcases le_total X Y with hXY | hYX

  · have hXZero : X = 0 := by
      rw [min_eq_left hXY] at hMin
      exact hMin
    have hAmpY : h3TerminalBalanceAmplitudeAt u t = Y := by
      rw [h3TerminalBalanceAmplitudeAt]
      simpa only [X, Y] using (max_eq_right hXY)
    refine ⟨hAmplitudeExact, Or.inl ?_⟩
    constructor
    · dsimp only [X] at hXZero
      linarith
    · simpa only [Y] using hAmpY

  · have hYZero : Y = 0 := by
      rw [min_eq_right hYX] at hMin
      exact hMin
    have hAmpX : h3TerminalBalanceAmplitudeAt u t = X := by
      rw [h3TerminalBalanceAmplitudeAt]
      simpa only [X, Y] using (max_eq_left hYX)
    refine ⟨hAmplitudeExact, Or.inr ?_⟩
    constructor
    · dsimp only [Y] at hYZero
      linarith
    · simpa only [X] using hAmpX

/-- A positive subordinate channel makes both signed balance channels positive;
equivalently both physical derivatives are strictly negative. -/
theorem h3TerminalBalanceCritical_positiveSubordinate_physicalSigns
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hPositive : 0 < h3TerminalBalanceSubordinateChannelAt u t) :
    deriv (velocityH3EnergyAt u) t < 0
      ∧ velocityH3TransportDerivativeAt u t < 0 := by
  have hDecayLower :
      h3TerminalBalanceSubordinateChannelAt u t
        ≤ - deriv (velocityH3EnergyAt u) t := by
    unfold h3TerminalBalanceSubordinateChannelAt
    exact min_le_left _ _

  have hTransportLower :
      h3TerminalBalanceSubordinateChannelAt u t
        ≤ - velocityH3TransportDerivativeAt u t := by
    unfold h3TerminalBalanceSubordinateChannelAt
    exact min_le_right _ _

  constructor <;> linarith

/-- Physical interpretation of a sign-resolved critical subordinate frontier. -/
def H3TerminalBalanceCriticalSubordinatePhysicalRegimeAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  H3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong u T τ
    ∧
  (
    (
      (∀ n : ℕ,
        h3TerminalBalanceSubordinateChannelAt u (τ n) < 0)
        ∧
      (∀ n : ℕ,
        (
          h3TerminalBalanceSubordinateChannelAt u (τ n)
              = - deriv (velocityH3EnergyAt u) (τ n)
            ∧
          h3TerminalBalanceAmplitudeAt u (τ n)
              = - velocityH3TransportDerivativeAt u (τ n)
            ∧
          0 < deriv (velocityH3EnergyAt u) (τ n)
        )
          ∨
        (
          h3TerminalBalanceSubordinateChannelAt u (τ n)
              = - velocityH3TransportDerivativeAt u (τ n)
            ∧
          h3TerminalBalanceAmplitudeAt u (τ n)
              = - deriv (velocityH3EnergyAt u) (τ n)
            ∧
          0 < velocityH3TransportDerivativeAt u (τ n)
        ))
    )
      ∨
    (
      (∀ n : ℕ,
        h3TerminalBalanceSubordinateChannelAt u (τ n) = 0)
        ∧
      (∀ n : ℕ,
        h3TerminalBalanceAmplitudeAt u (τ n)
            = 2 * velocityH3DissipationAt u (τ n)
          ∧
        (
          (deriv (velocityH3EnergyAt u) (τ n) = 0
            ∧ h3TerminalBalanceAmplitudeAt u (τ n)
                = - velocityH3TransportDerivativeAt u (τ n))
            ∨
          (velocityH3TransportDerivativeAt u (τ n) = 0
            ∧ h3TerminalBalanceAmplitudeAt u (τ n)
                = - deriv (velocityH3EnergyAt u) (τ n))
        ))
    )
      ∨
    (
      (∀ n : ℕ,
        0 < h3TerminalBalanceSubordinateChannelAt u (τ n))
        ∧
      (∀ n : ℕ,
        deriv (velocityH3EnergyAt u) (τ n) < 0
          ∧ velocityH3TransportDerivativeAt u (τ n) < 0)
    )
  )

/-- Every sign-resolved critical subordinate sequence has the corresponding
physical cancellation, exact-balance, or cooperative interpretation. -/
theorem h3TerminalBalanceCriticalSubordinatePhysicalRegimeAlong_of_signResolved
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hResolved :
      H3TerminalBalanceCriticalSubordinateSignResolvedAlong u T τ) :
    H3TerminalBalanceCriticalSubordinatePhysicalRegimeAlong u T τ := by
  rcases hResolved with ⟨hFrontier, hNegative | hZero | hPositive⟩

  · refine ⟨hFrontier, Or.inl ⟨hNegative, ?_⟩⟩
    intro n
    exact
      h3TerminalBalanceCancellation_orientation_of_subordinate_negative
        (hNegative n)

  · refine ⟨hFrontier, Or.inr (Or.inl ⟨hZero, ?_⟩)⟩
    intro n
    exact
      h3TerminalBalanceCritical_zeroSubordinate_geometry
        hH3 hClass (hAt n) (hZero n)

  · refine ⟨hFrontier, Or.inr (Or.inr ⟨hPositive, ?_⟩)⟩
    intro n
    exact
      h3TerminalBalanceCritical_positiveSubordinate_physicalSigns
        (hPositive n)

/-- At critical half-share, one cofinal subsequence carries a fixed subordinate
sign together with its complete physical interpretation and three-scale
frontier. -/
theorem exists_fixed_balanceCriticalSubordinatePhysicalRegime_subsequence_of_shareCluster_eq_half
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
      H3TerminalBalanceCriticalSubordinatePhysicalRegimeAlong
        u T (fun n : ℕ => τ (k n)) := by
  obtain ⟨k, hKMono, hClusterSub, hSignResolved⟩ :=
    exists_fixed_balanceCriticalSubordinateSign_subsequence_of_shareCluster_eq_half
      hH3 hNoExtension hClass hAt hCluster hTheta

  have hAtSub :
      ∀ n : ℕ,
        τ (k n) ∈ Set.Ioo a T :=
    fun n => hAt (k n)

  have hPhysical :=
    h3TerminalBalanceCriticalSubordinatePhysicalRegimeAlong_of_signResolved
      hH3 hClass hAtSub hSignResolved

  exact ⟨k, hKMono, hClusterSub, hPhysical⟩

end

end Euclidean
end Bridge
end PrimeTensor
