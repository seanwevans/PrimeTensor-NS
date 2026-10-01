import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Raw.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Normalized.Dissipation.Rate

/-!
# Polynomial physical-clock and normalized rates for the canonical H³ balance amplitude

The canonical branch-free balance amplitude is

`B(t) = max (-E'(t)) (-T_H3(t))`.

Two quantitative refinements of the full-tail balance-amplitude cascade follow
from already-established dissipation rates.

First, the raw inverse-`8/3` estimate

`1 ≤ 81 K⁸ E₀(b) (T-t)⁸ B(t)³`

can be rewritten exactly as

`1 ≤ 81 K⁸ E₀(b) (T-t)⁵ ((T-t) B(t))³`.

Thus the physical balance clock itself has the necessary inverse-`5/3` scale.

Second, the full-energy normalized dissipation rate

`1 ≤ C_b (T-t)² (D(t)/E(t))³`

transfers pointwise through `D(t) ≤ B(t)` to

`1 ≤ C_b (T-t)² (B(t)/E(t))³`.

Hence the canonical balance amplitude normalized by full H³ energy has the
necessary inverse-`2/3` scale.  Exact arbitrarily-late subcritical
contrapositives are recorded for both rates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Hypothetical nonextension forces the physical clock of the canonical
balance amplitude to satisfy the inverse-`5/3` polynomial rate on a full
terminal tail. -/
theorem exists_terminalTail_balanceAmplitude_physicalClock_cubicRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        1 ≤
          81
            * h3PathSqrtEnergyRiccatiCoefficient ^ 8
            * velocityH3Energy0At u b
            * (T - t) ^ 5
            * ((T - t) * h3TerminalBalanceAmplitudeAt u t) ^ 3 := by
  obtain ⟨c, hc, hRaw⟩ :=
    exists_terminalTail_balanceAmplitude_raw_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  refine ⟨c, hc, ?_⟩
  intro t ht

  calc
    1 ≤
        81
          * h3PathSqrtEnergyRiccatiCoefficient ^ 8
          * (T - t) ^ 8
          * velocityH3Energy0At u b
          * h3TerminalBalanceAmplitudeAt u t ^ 3 :=
      hRaw t ht
    _ =
        81
          * h3PathSqrtEnergyRiccatiCoefficient ^ 8
          * velocityH3Energy0At u b
          * (T - t) ^ 5
          * ((T - t) * h3TerminalBalanceAmplitudeAt u t) ^ 3 := by
      ring

/-- Hypothetical nonextension forces the canonical balance amplitude normalized
by full H³ energy to satisfy the same inverse-`2/3` cubic terminal rate as full
normalized dissipation. -/
theorem exists_terminalTail_balanceAmplitude_div_energy_cubicRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        1 ≤
          3
            * h3PathSqrtEnergyRiccatiCoefficient ^ 2
            * (velocityH3Energy0At u b + 1)
            * (4 + 3 * velocityH3Energy0At u b) ^ 3
            * (T - t) ^ 2
            *
              (h3TerminalBalanceAmplitudeAt u t /
                velocityH3EnergyAt u t) ^ 3 := by
  obtain ⟨c, hc, hDissipation⟩ :=
    exists_terminalTail_normalized_dissipation_cubic_rate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  refine ⟨c, hc, ?_⟩
  intro t ht

  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hc.1 ht.1), ht.2⟩

  have hEnergyNonneg :
      0 ≤ velocityH3EnergyAt u t := by
    have hOne := one_le_velocityH3EnergyAt u t
    linarith

  have hDNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t

  have hDom :
      velocityH3DissipationAt u t ≤
        h3TerminalBalanceAmplitudeAt u t :=
    velocityH3DissipationAt_le_h3TerminalBalanceAmplitudeAt
      hH3 hClass htClass

  have hRatioDom :
      velocityH3DissipationAt u t /
          velocityH3EnergyAt u t ≤
        h3TerminalBalanceAmplitudeAt u t /
          velocityH3EnergyAt u t :=
    div_le_div_of_nonneg_right
      hDom
      hEnergyNonneg

  have hRatioNonneg :
      0 ≤
        velocityH3DissipationAt u t /
          velocityH3EnergyAt u t :=
    div_nonneg hDNonneg hEnergyNonneg

  have hCube :
      (velocityH3DissipationAt u t /
          velocityH3EnergyAt u t) ^ 3 ≤
        (h3TerminalBalanceAmplitudeAt u t /
          velocityH3EnergyAt u t) ^ 3 :=
    pow_le_pow_left₀
      hRatioNonneg
      hRatioDom
      3

  have hE0Nonneg :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b

  have hPrefactorNonneg :
      0 ≤
        3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (4 + 3 * velocityH3Energy0At u b) ^ 3
          * (T - t) ^ 2 := by
    positivity

  have hScaled :
      3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (4 + 3 * velocityH3Energy0At u b) ^ 3
          * (T - t) ^ 2
          *
            (velocityH3DissipationAt u t /
              velocityH3EnergyAt u t) ^ 3
        ≤
      3
          * h3PathSqrtEnergyRiccatiCoefficient ^ 2
          * (velocityH3Energy0At u b + 1)
          * (4 + 3 * velocityH3Energy0At u b) ^ 3
          * (T - t) ^ 2
          *
            (h3TerminalBalanceAmplitudeAt u t /
              velocityH3EnergyAt u t) ^ 3 :=
    mul_le_mul_of_nonneg_left
      hCube
      hPrefactorNonneg

  exact
    (hDissipation t ht).trans hScaled

/-- Arbitrarily-late strict violation of the inverse-`5/3` physical-clock rate
forces smooth continuation across `T`. -/
theorem exists_smoothContinuationExtension_of_balanceAmplitude_physicalClock_cubicRate_subcritical_arbitrarilyLate
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
          81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              * velocityH3Energy0At u b
              * (T - t) ^ 5
              * ((T - t) * h3TerminalBalanceAmplitudeAt u t) ^ 3
            < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension

  obtain ⟨c, hc, hRate⟩ :=
    exists_terminalTail_balanceAmplitude_physicalClock_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  obtain ⟨t, ht, hSub⟩ :=
    hSubcritical c hc

  exact
    (not_lt_of_ge (hRate t ht)) hSub

/-- Arbitrarily-late strict violation of the inverse-`2/3` full-energy
normalized balance-amplitude rate forces smooth continuation across `T`. -/
theorem exists_smoothContinuationExtension_of_balanceAmplitude_div_energy_cubicRate_subcritical_arbitrarilyLate
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
              * (4 + 3 * velocityH3Energy0At u b) ^ 3
              * (T - t) ^ 2
              *
                (h3TerminalBalanceAmplitudeAt u t /
                  velocityH3EnergyAt u t) ^ 3
            < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension

  obtain ⟨c, hc, hRate⟩ :=
    exists_terminalTail_balanceAmplitude_div_energy_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  obtain ⟨t, ht, hSub⟩ :=
    hSubcritical c hc

  exact
    (not_lt_of_ge (hRate t ht)) hSub

/-- Canonical midpoint specialization of the physical-clock polynomial rate. -/
theorem exists_terminalTail_balanceAmplitude_physicalClock_cubicRate_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        1 ≤
          81
            * h3PathSqrtEnergyRiccatiCoefficient ^ 8
            *
              velocityH3Energy0At
                u
                (h3BKMKineticTailMidpoint a T)
            * (T - t) ^ 5
            * ((T - t) * h3TerminalBalanceAmplitudeAt u t) ^ 3 := by
  exact
    exists_terminalTail_balanceAmplitude_physicalClock_cubicRate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

/-- Canonical midpoint specialization of the full-energy normalized cubic
balance-amplitude rate. -/
theorem exists_terminalTail_balanceAmplitude_div_energy_cubicRate_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
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
            *
              (4
                + 3
                  * velocityH3Energy0At
                      u
                      (h3BKMKineticTailMidpoint a T)) ^ 3
            * (T - t) ^ 2
            *
              (h3TerminalBalanceAmplitudeAt u t /
                velocityH3EnergyAt u t) ^ 3 := by
  exact
    exists_terminalTail_balanceAmplitude_div_energy_cubicRate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
