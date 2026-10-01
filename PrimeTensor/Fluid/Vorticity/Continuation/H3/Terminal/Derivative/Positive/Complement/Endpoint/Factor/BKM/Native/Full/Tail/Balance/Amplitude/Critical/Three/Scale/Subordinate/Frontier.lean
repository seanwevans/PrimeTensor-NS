import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Critical.Normalized.Subordinate.Frontier

/-!
# Critical three-scale subordinate frontier

At critical half-share the same vanishing relative factor

`S / (2D) -> 0`

controls all three still-unresolved subordinate scales.  The corresponding
full-dissipation scales diverge in raw, physical-clock, and energy-normalized
units, and the subordinate quantity factors exactly through that same relative
share:

* `S = (S / (2D)) * (2D)`,
* `(T-t) S = (S / (2D)) * ((T-t) (2D))`,
* `S / E = (S / (2D)) * ((2D) / E)`.

Thus each remaining subordinate rate is a `0 * ∞` product governed by one common
vanishing factor.  No limit or sign is asserted for the products themselves.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem two_mul_tendsto_atTop_criticalSubordinate
    {f : ℕ → ℝ}
    (hf : Tendsto f atTop atTop) :
    Tendsto (fun n : ℕ => 2 * f n) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  have hEventually :
      ∀ᶠ n : ℕ in atTop, M / 2 ≤ f n :=
    hf.eventually (eventually_ge_atTop (M / 2))
  filter_upwards [hEventually] with n hn
  linarith

/-- The complete critical subordinate frontier in raw, physical-clock, and
energy-normalized units.  One common relative factor tends to zero, while all
three corresponding twice-dissipation scales diverge. -/
def H3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (0 : ℝ))
    ∧
  Tendsto
      (fun n : ℕ =>
        2 * velocityH3DissipationAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (T - τ n) * (2 * velocityH3DissipationAt u (τ n)))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (2 * velocityH3DissipationAt u (τ n)) /
          velocityH3EnergyAt u (τ n))
      atTop atTop
    ∧
  (
    (fun n : ℕ =>
      h3TerminalBalanceSubordinateChannelAt u (τ n))
      =ᶠ[atTop]
    (fun n : ℕ =>
      (h3TerminalBalanceSubordinateChannelAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
        *
      (2 * velocityH3DissipationAt u (τ n)))
  )
    ∧
  (
    (fun n : ℕ =>
      (T - τ n) * h3TerminalBalanceSubordinateChannelAt u (τ n))
      =ᶠ[atTop]
    (fun n : ℕ =>
      (h3TerminalBalanceSubordinateChannelAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
        *
      ((T - τ n) * (2 * velocityH3DissipationAt u (τ n))))
  )
    ∧
  (
    (fun n : ℕ =>
      h3TerminalBalanceSubordinateChannelAt u (τ n) /
        velocityH3EnergyAt u (τ n))
      =ᶠ[atTop]
    (fun n : ℕ =>
      (h3TerminalBalanceSubordinateChannelAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
        *
      ((2 * velocityH3DissipationAt u (τ n)) /
          velocityH3EnergyAt u (τ n)))
  )

/-- At critical half-share, the raw, physical-clock, and energy-normalized
subordinate channels are all governed by the same vanishing-times-divergent
factorization. -/
theorem h3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong_of_shareCluster_eq_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2) :
    H3TerminalBalanceCriticalThreeScaleSubordinateFrontierAlong u T τ := by
  have hNormalized :
      H3TerminalBalanceCriticalNormalizedSubordinateFrontierAlong u τ :=
    h3TerminalBalanceCriticalNormalizedSubordinateFrontierAlong_of_shareCluster_eq_half
      hH3 hClass hAt hCluster hTheta

  have hCriticalCascade :
      H3TerminalBalanceCriticalDissipationImbalanceClockCascadeAlong u T τ :=
    h3TerminalBalanceCriticalDissipationImbalanceClockCascadeAlong_of_shareCluster_eq_half
      hAt hCluster hTheta

  have hTwoDRaw :
      Tendsto
        (fun n : ℕ => 2 * velocityH3DissipationAt u (τ n))
        atTop atTop :=
    two_mul_tendsto_atTop_criticalSubordinate hCriticalCascade.1

  have hTwoDClockScaled :
      Tendsto
        (fun n : ℕ =>
          2 * ((T - τ n) * velocityH3DissipationAt u (τ n)))
        atTop atTop :=
    two_mul_tendsto_atTop_criticalSubordinate hCriticalCascade.2.1

  have hClockFunction :
      (fun n : ℕ =>
        2 * ((T - τ n) * velocityH3DissipationAt u (τ n)))
        =
      (fun n : ℕ =>
        (T - τ n) * (2 * velocityH3DissipationAt u (τ n))) := by
    funext n
    ring

  have hTwoDClock :
      Tendsto
        (fun n : ℕ =>
          (T - τ n) * (2 * velocityH3DissipationAt u (τ n)))
        atTop atTop := by
    rw [← hClockFunction]
    exact hTwoDClockScaled

  have hDPos :
      ∀ᶠ n : ℕ in atTop,
        0 < velocityH3DissipationAt u (τ n) :=
    hCriticalCascade.1.eventually
      (eventually_gt_atTop (0 : ℝ))

  have hRawFactorization :
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n))
        =ᶠ[atTop]
      (fun n : ℕ =>
        (h3TerminalBalanceSubordinateChannelAt u (τ n) /
            (2 * velocityH3DissipationAt u (τ n)))
          *
        (2 * velocityH3DissipationAt u (τ n))) := by
    filter_upwards [hDPos] with n hDn
    have hTwoDNe :
        2 * velocityH3DissipationAt u (τ n) ≠ 0 := by
      positivity
    field_simp [hTwoDNe]

  have hClockFactorization :
      (fun n : ℕ =>
        (T - τ n) * h3TerminalBalanceSubordinateChannelAt u (τ n))
        =ᶠ[atTop]
      (fun n : ℕ =>
        (h3TerminalBalanceSubordinateChannelAt u (τ n) /
            (2 * velocityH3DissipationAt u (τ n)))
          *
        ((T - τ n) * (2 * velocityH3DissipationAt u (τ n)))) := by
    filter_upwards [hDPos] with n hDn
    have hTwoDNe :
        2 * velocityH3DissipationAt u (τ n) ≠ 0 := by
      positivity
    field_simp [hTwoDNe]
    <;> ring

  exact
    ⟨
      hNormalized.1,
      hTwoDRaw,
      hTwoDClock,
      hNormalized.2.1,
      hRawFactorization,
      hClockFactorization,
      hNormalized.2.2
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
