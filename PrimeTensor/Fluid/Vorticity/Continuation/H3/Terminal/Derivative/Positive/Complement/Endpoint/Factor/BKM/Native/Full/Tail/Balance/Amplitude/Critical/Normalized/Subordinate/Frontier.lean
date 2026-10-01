import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Critical.Channel.Geometry

/-!
# Critical normalized subordinate frontier

At critical half-share the subordinate signed balance channel is negligible
relative to twice full H³ dissipation, while full dissipation divided by energy
diverges.  Hence the still-unresolved normalized subordinate rate has the exact
eventual factorization

`S / E = (S / (2D)) * ((2D) / E)`

with the first factor tending to `0` and the second to `+∞`.

This records the remaining `0 * ∞` frontier without assigning a limit or sign
to `S / E` that is not forced by the present estimates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The exact unresolved normalized subordinate structure at critical half-share:
`S/(2D) -> 0`, `(2D)/E -> +∞`, and eventually
`S/E = (S/(2D))*((2D)/E)`. -/
def H3TerminalBalanceCriticalNormalizedSubordinateFrontierAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) : Prop :=
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          (2 * velocityH3DissipationAt u (τ n)))
      atTop (𝓝 (0 : ℝ))
    ∧
  Tendsto
      (fun n : ℕ =>
        (2 * velocityH3DissipationAt u (τ n)) /
          velocityH3EnergyAt u (τ n))
      atTop atTop
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

/-- Critical half-share leaves precisely a vanishing-times-divergent product for
the energy-normalized subordinate channel. -/
theorem h3TerminalBalanceCriticalNormalizedSubordinateFrontierAlong_of_shareCluster_eq_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta = (1 : ℝ) / 2) :
    H3TerminalBalanceCriticalNormalizedSubordinateFrontierAlong u τ := by
  have hEquip : H3TerminalBalanceCriticalEquipartitionAlong u τ :=
    h3TerminalBalanceCriticalEquipartitionAlong_of_shareCluster_eq_half
      hH3 hClass hAt hCluster hTheta

  have hCriticalCascade :
      H3TerminalBalanceCriticalDissipationImbalanceClockCascadeAlong u T τ :=
    h3TerminalBalanceCriticalDissipationImbalanceClockCascadeAlong_of_shareCluster_eq_half
      hAt hCluster hTheta

  have hDNormalized :
      Tendsto
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ n) /
            velocityH3EnergyAt u (τ n))
        atTop atTop :=
    hCriticalCascade.2.2.1

  have hTwoDNormalized :
      Tendsto
        (fun n : ℕ =>
          (2 * velocityH3DissipationAt u (τ n)) /
            velocityH3EnergyAt u (τ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          M / 2 ≤
            velocityH3DissipationAt u (τ n) /
              velocityH3EnergyAt u (τ n) :=
      hDNormalized.eventually (eventually_ge_atTop (M / 2))
    filter_upwards [hEventually] with n hn
    have hScaled :
        M ≤
          2 *
            (velocityH3DissipationAt u (τ n) /
              velocityH3EnergyAt u (τ n)) := by
      linarith
    simpa only [mul_div_assoc] using hScaled

  have hDPos :
      ∀ᶠ n : ℕ in atTop,
        0 < velocityH3DissipationAt u (τ n) :=
    hCriticalCascade.1.eventually
      (eventually_gt_atTop (0 : ℝ))

  have hFactorization :
      (fun n : ℕ =>
        h3TerminalBalanceSubordinateChannelAt u (τ n) /
          velocityH3EnergyAt u (τ n))
        =ᶠ[atTop]
      (fun n : ℕ =>
        (h3TerminalBalanceSubordinateChannelAt u (τ n) /
            (2 * velocityH3DissipationAt u (τ n)))
          *
        ((2 * velocityH3DissipationAt u (τ n)) /
            velocityH3EnergyAt u (τ n))) := by
    filter_upwards [hDPos] with n hDn
    have hTwoDNe :
        2 * velocityH3DissipationAt u (τ n) ≠ 0 := by
      positivity
    have hENe :
        velocityH3EnergyAt u (τ n) ≠ 0 := by
      have hOne := one_le_velocityH3EnergyAt u (τ n)
      linarith
    field_simp [hTwoDNe, hENe]

  exact
    ⟨
      hEquip.2.2,
      hTwoDNormalized,
      hFactorization
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
