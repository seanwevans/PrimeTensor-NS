import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Cubic.Threshold.Continuation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.Eventual

/-!
# Raw inverse-eight-thirds rate for the canonical H³ balance amplitude

The canonical branch-free balance amplitude is

`B(t) = max (-E'(t)) (-T_H3(t))`.

The established top-order dissipation rate says that hypothetical nonextension
forces, after a fixed strict anchor `b`, a sufficiently late terminal tail on
which

`1 ≤ 81 K⁸ (T-t)⁸ E₀(b) D₃(t)³`.

Exact balance gives `D₃(t) ≤ D(t) ≤ B(t)`.  Therefore the same polynomial
terminal rate transfers directly to the canonical amplitude:

`1 ≤ 81 K⁸ (T-t)⁸ E₀(b) B(t)³`.

Equivalently, the branch-free balance amplitude has the necessary raw scale
`B(t) ≳ (T-t)^(-8/3)` under hypothetical nonextension.  No energy-derivative
sign and no decay/transport branch selection is used.

The exact contrapositive is also recorded: an arbitrarily-late strict violation
of this raw cubic rate forces smooth continuation across `T`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Hypothetical nonextension forces the raw canonical balance amplitude to
satisfy the same inverse-`8/3` polynomial rate as the top H³ dissipation block
on some full terminal tail. -/
theorem exists_terminalTail_balanceAmplitude_raw_cubicRate_of_noH3PathExtension
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
            * (T - t) ^ 8
            * velocityH3Energy0At u b
            * h3TerminalBalanceAmplitudeAt u t ^ 3 := by
  obtain ⟨c, hc, hTopRate⟩ :=
    exists_terminalTail_topH3DissipationRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  refine ⟨c, hc, ?_⟩
  intro t ht

  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hc.1 ht.1), ht.2⟩

  have hD3Nonneg :
      0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg u t

  have hDom :
      velocityH3Dissipation3At u t ≤
        h3TerminalBalanceAmplitudeAt u t :=
    velocityH3Dissipation3At_le_h3TerminalBalanceAmplitudeAt
      hH3 hClass htClass

  have hCube :
      velocityH3Dissipation3At u t ^ 3 ≤
        h3TerminalBalanceAmplitudeAt u t ^ 3 :=
    pow_le_pow_left₀
      hD3Nonneg
      hDom
      3

  have hE0Nonneg :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b

  have hPrefactorNonneg :
      0 ≤
        81
          * h3PathSqrtEnergyRiccatiCoefficient ^ 8
          * (T - t) ^ 8
          * velocityH3Energy0At u b := by
    positivity

  have hScaled :
      81
          * h3PathSqrtEnergyRiccatiCoefficient ^ 8
          * (T - t) ^ 8
          * velocityH3Energy0At u b
          * velocityH3Dissipation3At u t ^ 3
        ≤
      81
          * h3PathSqrtEnergyRiccatiCoefficient ^ 8
          * (T - t) ^ 8
          * velocityH3Energy0At u b
          * h3TerminalBalanceAmplitudeAt u t ^ 3 :=
    mul_le_mul_of_nonneg_left
      hCube
      hPrefactorNonneg

  exact
    (hTopRate t ht).trans hScaled

/-- If the raw inverse-`8/3` balance-amplitude rate is strictly violated at
arbitrarily late times beyond a fixed strict anchor, then the H³ path extends
smoothly across `T`. -/
theorem exists_smoothContinuationExtension_of_balanceAmplitude_raw_cubicRate_subcritical_arbitrarilyLate
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
              * (T - t) ^ 8
              * velocityH3Energy0At u b
              * h3TerminalBalanceAmplitudeAt u t ^ 3
            < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension

  obtain ⟨c, hc, hRate⟩ :=
    exists_terminalTail_balanceAmplitude_raw_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  obtain ⟨t, ht, hSub⟩ :=
    hSubcritical c hc

  exact
    (not_lt_of_ge (hRate t ht)) hSub

/-- Neutral quantitative alternative: either smooth continuation exists, or the
raw inverse-`8/3` canonical balance-amplitude rate holds throughout some later
terminal tail. -/
theorem smoothContinuationExtension_or_eventual_balanceAmplitude_raw_cubicRate
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
            81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              * (T - t) ^ 8
              * velocityH3Energy0At u b
              * h3TerminalBalanceAmplitudeAt u t ^ 3
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (exists_terminalTail_balanceAmplitude_raw_cubicRate_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor form of the eventual raw balance-amplitude rate. -/
theorem exists_terminalTail_balanceAmplitude_raw_cubicRate_midpoint_of_noH3PathExtension
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
            * (T - t) ^ 8
            *
              velocityH3Energy0At
                u
                (h3BKMKineticTailMidpoint a T)
            * h3TerminalBalanceAmplitudeAt u t ^ 3 := by
  exact
    exists_terminalTail_balanceAmplitude_raw_cubicRate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

/-- Canonical midpoint-anchor form of the arbitrarily-late subcritical raw
balance-amplitude continuation criterion. -/
theorem exists_smoothContinuationExtension_of_balanceAmplitude_raw_cubicRate_subcritical_arbitrarilyLate_midpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hSubcritical :
      ∀ c : ℝ,
        c ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          81
              * h3PathSqrtEnergyRiccatiCoefficient ^ 8
              * (T - t) ^ 8
              *
                velocityH3Energy0At
                  u
                  (h3BKMKineticTailMidpoint a T)
              * h3TerminalBalanceAmplitudeAt u t ^ 3
            < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  exact
    exists_smoothContinuationExtension_of_balanceAmplitude_raw_cubicRate_subcritical_arbitrarilyLate
      hH3
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)
      hSubcritical

end

end Euclidean
end Bridge
end PrimeTensor
