import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeFrequencyBridge

/-!
# Cubic threshold continuation from the canonical balance amplitude

The intrinsic frequency bridge proves that hypothetical nonextension forces,
for every fixed strict terminal anchor `b`, a sufficiently late tail on which

`1 ≤ 3 K² (E₀(b)+1) (T-t)² (B(t)/E₃(t))³`,

where

`B(t) = max (-E'(t)) (-T_H3(t))`

is the canonical branch-free balance amplitude.

This file records the exact positive contrapositive.  If that dimensionless
cubic quantity is strictly below `1` at arbitrarily late times, then smooth
continuation across `T` exists.  The statement keeps the decay/transport split
completely unresolved and uses only the canonical amplitude.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- If the intrinsic cubic balance-amplitude rate is subcritical at arbitrarily
late times beyond a fixed strict anchor, then the H³ path extends smoothly
across `T`. -/
theorem exists_smoothContinuationExtension_of_balanceAmplitude_div_energy3_cubicRate_subcritical_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hSubcritical :
      ∀ c : ℝ,
        c ∈ Set.Ioo b T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          3
              * h3PathSqrtEnergyRiccatiCoefficient ^ 2
              * (velocityH3Energy0At u b + 1)
              * (T - t) ^ 2
              *
                (h3TerminalBalanceAmplitudeAt u t /
                  velocityH3Energy3At u t) ^ 3
            < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension

  obtain ⟨c, hc, hRate⟩ :=
    exists_terminalTail_balanceAmplitude_div_energy3_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  obtain ⟨t, ht, hSub⟩ :=
    hSubcritical c hc

  exact
    (not_lt_of_ge (hRate t ht)) hSub

/-- Neutral quantitative form: for a fixed strict terminal anchor, either a
smooth continuation exists or the intrinsic cubic balance-amplitude lower rate
holds throughout some later tail. -/
theorem smoothContinuationExtension_or_eventual_balanceAmplitude_div_energy3_cubicRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃ c : ℝ,
        c ∈ Set.Ioo b T
          ∧
        ∀ t : ℝ,
          t ∈ Set.Ioo c T →
          1 ≤
            3
              * h3PathSqrtEnergyRiccatiCoefficient ^ 2
              * (velocityH3Energy0At u b + 1)
              * (T - t) ^ 2
              *
                (h3TerminalBalanceAmplitudeAt u t /
                  velocityH3Energy3At u t) ^ 3
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (exists_terminalTail_balanceAmplitude_div_energy3_cubicRate_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor specialization of the arbitrarily-late
subcritical cubic balance-amplitude continuation criterion. -/
theorem exists_smoothContinuationExtension_of_balanceAmplitude_div_energy3_cubicRate_subcritical_arbitrarilyLate_midpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hSubcritical :
      ∀ c : ℝ,
        c ∈
          Set.Ioo
            (h3BKMKineticTailMidpoint a T)
            T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          3
              * h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
                (velocityH3Energy0At
                    u
                    (h3BKMKineticTailMidpoint a T)
                  + 1)
              * (T - t) ^ 2
              *
                (h3TerminalBalanceAmplitudeAt u t /
                  velocityH3Energy3At u t) ^ 3
            < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  exact
    exists_smoothContinuationExtension_of_balanceAmplitude_div_energy3_cubicRate_subcritical_arbitrarilyLate
      hH3
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)
      hSubcritical

/-- Canonical midpoint neutral form of the intrinsic cubic balance-amplitude
terminal alternative. -/
theorem smoothContinuationExtension_or_eventual_balanceAmplitude_div_energy3_cubicRate_midpoint
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
      ∃ c : ℝ,
        c ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T
          ∧
        ∀ t : ℝ,
          t ∈ Set.Ioo c T →
          1 ≤
            3
              * h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
                (velocityH3Energy0At
                    u
                    (h3BKMKineticTailMidpoint a T)
                  + 1)
              * (T - t) ^ 2
              *
                (h3TerminalBalanceAmplitudeAt u t /
                  velocityH3Energy3At u t) ^ 3
    ) := by
  exact
    smoothContinuationExtension_or_eventual_balanceAmplitude_div_energy3_cubicRate
      hH3
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
