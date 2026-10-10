import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceKineticLimitCubicClock
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Energy.Kinetic.Monotonicity
import Mathlib.Topology.Order.Monotone

/-!
# Automatic terminal kinetic limit and optimized full H³ cubic clock

The prior full H³ terminal cubic clock was optimized under an explicitly
assumed finite kinetic limit `E₀(t) -> L`. With canonical H³ energy data,
order-zero kinetic energy is antitone on `(a,T)` and nonnegative everywhere.
Mathlib's left-limit theorem for antitone functions therefore proves the
missing limit automatically, with

  L = sInf (E₀ '' Ioo a T),      0 <= L <= E₀(b), for b in (a,T).

Consequently all previously established kinetic-limit cubic clock and
continuation conclusions hold under canonical H³ energy data, without any
independent kinetic-limit hypothesis. The same fixed ten-source witness and
both exhaustive signed-source alternatives remain unchanged. These results
remain conditional on their H³ energy-class and analytic data hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Terminal kinetic energy defined as the infimum of the nonnegative,
nonincreasing kinetic energy on the canonical open energy-class tail. -/
noncomputable def h3PathCanonicalTerminalKineticEnergyAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : ℝ :=
  sInf (velocityH3Energy0At u '' Set.Ioo a T)

/-- The canonical interval is nonempty, hence so is its kinetic image. -/
private theorem h3PathCanonical_kineticTailImage_nonempty
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ} (haT : a < T) :
    (velocityH3Energy0At u '' Set.Ioo a T).Nonempty := by
  refine ⟨velocityH3Energy0At u (h3BKMKineticTailMidpoint a T), ?_⟩
  exact ⟨h3BKMKineticTailMidpoint a T,
    h3BKMKineticTailMidpoint_mem_Ioo haT, rfl⟩

/-- Nonnegativity of kinetic energy bounds its terminal image below. -/
private theorem h3PathCanonical_kineticTailImage_bddBelow
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) :
    BddBelow (velocityH3Energy0At u '' Set.Ioo a T) := by
  refine ⟨0, ?_⟩
  rintro y ⟨t, _ht, rfl⟩
  exact velocityH3Energy0At_nonneg u t

/-- The automatic terminal kinetic energy is finite and nonnegative. -/
theorem h3PathCanonical_terminalKineticEnergy_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ} (hClass : PreterminalH3EnergyClass u a T) :
    0 ≤ h3PathCanonicalTerminalKineticEnergyAt u a T := by
  unfold h3PathCanonicalTerminalKineticEnergyAt
  apply le_csInf
    (h3PathCanonical_kineticTailImage_nonempty hClass.terminal_start.2)
  rintro y ⟨t, _ht, rfl⟩
  exact velocityH3Energy0At_nonneg u t

/-- Every strict kinetic anchor lies above the terminal infimum. -/
theorem h3PathCanonical_terminalKineticEnergy_le_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T b : ℝ} (hb : b ∈ Set.Ioo a T) :
    h3PathCanonicalTerminalKineticEnergyAt u a T ≤
      velocityH3Energy0At u b := by
  unfold h3PathCanonicalTerminalKineticEnergyAt
  exact csInf_le (h3PathCanonical_kineticTailImage_bddBelow u a T)
    ⟨b, hb, rfl⟩

/-- Canonical H³ energy data automatically yield a finite left-terminal
kinetic limit, by antitonicity and its global nonnegative floor. -/
theorem h3PathCanonical_terminalKineticEnergy_tendsto_of_canonical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T) :
    Tendsto (velocityH3Energy0At u) (𝓝[<] T)
      (𝓝 (h3PathCanonicalTerminalKineticEnergyAt u a T)) := by
  have hNonempty : (Set.Ioo a T).Nonempty :=
    ⟨h3BKMKineticTailMidpoint a T,
      h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2⟩
  have hAnti := antitoneOn_velocityH3Energy0At_of_energyClass_canonical
    hClass hData
  have hBdd := h3PathCanonical_kineticTailImage_bddBelow u a T
  change Tendsto (velocityH3Energy0At u) (𝓝[<] T)
    (𝓝 (sInf (velocityH3Energy0At u '' Set.Ioo a T)))
  exact AntitoneOn.tendsto_nhdsWithin_Ioo_left hNonempty hAnti hBdd

/-- The limiting kinetic coefficient is no larger than the coefficient
at any earlier strict tail anchor. -/
theorem h3PathCanonical_terminalKineticCoefficient_le_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T b : ℝ} (hb : b ∈ Set.Ioo a T) :
    h3PathCanonicalKineticLimitCubicCoefficient
        (h3PathCanonicalTerminalKineticEnergyAt u a T) ≤
      h3PathCanonicalKineticCubicCoefficientAt u b := by
  have hInf : h3PathCanonicalTerminalKineticEnergyAt u a T ≤
      velocityH3Energy0At u b :=
    h3PathCanonical_terminalKineticEnergy_le_anchor (u := u) hb
  have hShift : h3PathCanonicalTerminalKineticEnergyAt u a T + 1 ≤
      velocityH3Energy0At u b + 1 := by
    linarith only [hInf]
  have hFactor : 0 ≤ 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 := by
    positivity
  change 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (h3PathCanonicalTerminalKineticEnergyAt u a T + 1) ≤
    3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1)
  exact mul_le_mul_of_nonneg_left hShift hFactor

/-- Without an independent limit hypothesis, the kinetic cubic coefficient
converges to its canonical, intrinsically defined terminal coefficient. -/
theorem h3PathCanonical_kineticCoefficient_tendsto_canonicalLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T) :
    Tendsto (h3PathCanonicalKineticCubicCoefficientAt u) (𝓝[<] T)
      (𝓝 (h3PathCanonicalKineticLimitCubicCoefficient
        (h3PathCanonicalTerminalKineticEnergyAt u a T))) := by
  exact h3PathCanonical_kineticCoefficient_tendsto_terminalLimit
    (h3PathCanonical_terminalKineticEnergy_tendsto_of_canonical hClass hData)

/-- Under canonical analytic H³ energy data, nonextension forces the
optimized, terminal-kinetic cubic clock above every strict subunit level
on the complete physical left terminal neighborhood. -/
theorem h3PathCanonical_canonicalKineticLimit_sharpCubicClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (q : ℝ) (hq : q < 1) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      q ≤ h3PathCanonicalKineticLimitCubicCoefficient
        (h3PathCanonicalTerminalKineticEnergyAt u a T) *
          h3PathCanonicalFullCubicRateAt u T t := by
  exact h3PathCanonical_terminalKineticLimit_sharpCubicClock
    hH3 hNoExtension hClass
    (h3PathCanonical_terminalKineticEnergy_tendsto_of_canonical hClass hData)
    (h3PathCanonical_terminalKineticEnergy_nonneg hClass) q hq

/-- A strictly subcritical full H³ cubic-rate ceiling forces continuation
without separately hypothesizing existence of a finite kinetic limit. -/
theorem h3PathCanonical_smoothExtension_of_canonicalKineticLimit_rateCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (hRate : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalFullCubicRateAt u T t ≤ B)
    (hStrict : h3PathCanonicalKineticLimitCubicCoefficient
      (h3PathCanonicalTerminalKineticEnergyAt u a T) * B < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  exact h3PathCanonical_smoothExtension_of_terminalKineticLimit_rateCeiling
    hH3 hClass
    (h3PathCanonical_terminalKineticEnergy_tendsto_of_canonical hClass hData)
    hRate hStrict

/-- The optimized continuation criterion also holds along any preselected
left-terminal sequence, including an existing directed-source witness. -/
theorem h3PathCanonical_smoothExtension_of_canonicalKineticLimit_sequenceRateCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (tau : ℕ → ℝ)
    (hTau : Tendsto tau atTop (𝓝[<] T))
    (hRate : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalFullCubicRateAt u T (tau n) ≤ B)
    (hStrict : h3PathCanonicalKineticLimitCubicCoefficient
      (h3PathCanonicalTerminalKineticEnergyAt u a T) * B < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  exact h3PathCanonical_smoothExtension_of_terminalKineticLimit_sequenceRateCeiling
    hH3 hClass
    (h3PathCanonical_terminalKineticEnergy_tendsto_of_canonical hClass hData)
    tau hTau hRate hStrict

/-- The SAME ten-source index, localized physical witness, critical clocks
and exhaustive sign branches carry the canonical terminal-kinetic cubic
threshold without assuming a limit in addition to canonical energy data. -/
theorem h3PathCanonical_fixedDirectedSource_canonicalKineticLimitSharpCubicClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (tau : ℕ → ℝ),
      (∀ n : ℕ,
        tau n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (tau n) i /
            (9 * velocityH3EnergyAt u (tau n))) ∧
      Tendsto tau atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3Energy3At u (tau n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalFullToTopPhysicalLengthRatioAt u (tau n))
        atTop (𝓝 1) ∧
      (∀ q : ℝ, q < 1 →
        ∀ᶠ n : ℕ in atTop,
          q ≤ h3PathCanonicalKineticLimitCubicCoefficient
            (h3PathCanonicalTerminalKineticEnergyAt u a T) *
              h3PathCanonicalFullCubicRateAt u T (tau n)) ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (tau n)) ∧
      ((i = 0 ∧
          (∀ n : ℕ,
            h3PathCanonicalGradientFullDissipationBudgetAt u (tau n) (n : ℝ)) ∧
          (∀ᶠ n : ℕ in atTop,
            h3PathCanonicalGradientTopShareClockAt u T b (tau n) (n : ℝ))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            ∀ n : ℕ,
              (n : ℝ) <
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (tau n) j r) /
                  velocityH3EnergyAt u (tau n))) := by
  exact h3PathCanonical_fixedDirectedSource_kineticLimitSharpCubicClock
    hH3 hNoExtension hClass hb
    (h3PathCanonical_terminalKineticEnergy_tendsto_of_canonical hClass hData)
    (h3PathCanonical_terminalKineticEnergy_nonneg hClass)

end
end Euclidean
end Bridge
end PrimeTensor
