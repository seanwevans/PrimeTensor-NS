import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Clocks

/-!
# Canonical full-tail H³ balance amplitude

The preceding full-tail balance theorem keeps the two exact-balance channels
explicit:

* `-E'(t)`;
* `-T_H3(t)`.

Their pointwise maximum is the canonical branch-free balance amplitude

`B(t) = max (-E'(t)) (-T_H3(t))`.

Exact balance already shows `D(t) ≤ B(t)` at every strict energy-class time.
Consequently all three previously forced dissipation scales transfer directly
to this single amplitude under hypothetical nonextension:

* `B(t) -> +∞`;
* `(T-t) B(t) -> +∞`;
* `B(t) / E(t) -> +∞`.

This packages the terminal balance obstruction without choosing between rapid
energy decay and adverse transport, and remains valid under arbitrary switching
between those channels.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Canonical branch-free H³ balance amplitude. -/
def h3TerminalBalanceAmplitudeAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  max
    (- deriv (velocityH3EnergyAt u) t)
    (- velocityH3TransportDerivativeAt u t)

/-- Full H³ dissipation is bounded by the canonical balance amplitude at every
strict energy-class time. -/
theorem velocityH3DissipationAt_le_h3TerminalBalanceAmplitudeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3DissipationAt u t ≤
      h3TerminalBalanceAmplitudeAt u t := by
  simpa [h3TerminalBalanceAmplitudeAt] using
    velocityH3DissipationAt_le_max_negativeEnergyDerivative_negativeTransport
      hH3 hClass ht

/-- Hypothetical nonextension forces the raw branch-free balance amplitude to
 diverge throughout the entire left terminal neighborhood. -/
theorem h3TerminalBalanceAmplitudeAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (h3TerminalBalanceAmplitudeAt u)
      (𝓝[<] T)
      atTop := by
  have hD :=
    velocityH3DissipationAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass

  refine tendsto_atTop.2 ?_
  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M ≤ velocityH3DissipationAt u t :=
    hD.eventually
      (eventually_ge_atTop M)

  have hTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2

  filter_upwards [hEventually, hTail] with t hM ht

  exact
    le_trans
      hM
      (velocityH3DissipationAt_le_h3TerminalBalanceAmplitudeAt
        hH3 hClass ht)

/-- Hypothetical nonextension forces the physical terminal clock of the
branch-free balance amplitude to diverge on the full left terminal tail. -/
theorem h3TerminalBalanceAmplitudePhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (fun t : ℝ =>
        (T - t) * h3TerminalBalanceAmplitudeAt u t)
      (𝓝[<] T)
      atTop := by
  have hDClock :=
    velocityH3DissipationPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass

  refine tendsto_atTop.2 ?_
  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M ≤ (T - t) * velocityH3DissipationAt u t :=
    hDClock.eventually
      (eventually_ge_atTop M)

  have hTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2

  filter_upwards [hEventually, hTail] with t hM ht

  have hGapNonneg : 0 ≤ T - t := by
    linarith [ht.2]

  have hDom :
      velocityH3DissipationAt u t ≤
        h3TerminalBalanceAmplitudeAt u t :=
    velocityH3DissipationAt_le_h3TerminalBalanceAmplitudeAt
      hH3 hClass ht

  have hScaled :
      (T - t) * velocityH3DissipationAt u t ≤
        (T - t) * h3TerminalBalanceAmplitudeAt u t :=
    mul_le_mul_of_nonneg_left
      hDom
      hGapNonneg

  exact le_trans hM hScaled

/-- Hypothetical nonextension forces the branch-free balance amplitude
normalized by full H³ energy to diverge on the full left terminal tail. -/
theorem h3TerminalBalanceAmplitudeNormalizedRate_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (fun t : ℝ =>
        h3TerminalBalanceAmplitudeAt u t /
          velocityH3EnergyAt u t)
      (𝓝[<] T)
      atTop := by
  have hRatio :=
    velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass

  refine tendsto_atTop.2 ?_
  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M ≤
          velocityH3DissipationAt u t /
            velocityH3EnergyAt u t :=
    hRatio.eventually
      (eventually_ge_atTop M)

  have hTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2

  filter_upwards [hEventually, hTail] with t hM ht

  have hEnergyNonneg :
      0 ≤ velocityH3EnergyAt u t := by
    have hOne := one_le_velocityH3EnergyAt u t
    linarith

  have hDom :
      velocityH3DissipationAt u t ≤
        h3TerminalBalanceAmplitudeAt u t :=
    velocityH3DissipationAt_le_h3TerminalBalanceAmplitudeAt
      hH3 hClass ht

  have hRatioDom :
      velocityH3DissipationAt u t /
          velocityH3EnergyAt u t ≤
        h3TerminalBalanceAmplitudeAt u t /
          velocityH3EnergyAt u t :=
    div_le_div_of_nonneg_right
      hDom
      hEnergyNonneg

  exact le_trans hM hRatioDom

/-- Neutral full-tail package for the canonical balance amplitude.  Either the
H³ path extends smoothly, or the raw amplitude, its physical clock, and its
full-energy normalized rate all diverge on the entire left terminal tail. -/
theorem smoothContinuationExtension_or_fullTailBalanceAmplitudeCascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      Tendsto
        (h3TerminalBalanceAmplitudeAt u)
        (𝓝[<] T)
        atTop
      ∧
      Tendsto
        (fun t : ℝ =>
          (T - t) * h3TerminalBalanceAmplitudeAt u t)
        (𝓝[<] T)
        atTop
      ∧
      Tendsto
        (fun t : ℝ =>
          h3TerminalBalanceAmplitudeAt u t /
            velocityH3EnergyAt u t)
        (𝓝[<] T)
        atTop
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        ⟨
          h3TerminalBalanceAmplitudeAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3 hExtension hClass,
          h3TerminalBalanceAmplitudePhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3 hExtension hClass,
          h3TerminalBalanceAmplitudeNormalizedRate_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3 hExtension hClass
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
