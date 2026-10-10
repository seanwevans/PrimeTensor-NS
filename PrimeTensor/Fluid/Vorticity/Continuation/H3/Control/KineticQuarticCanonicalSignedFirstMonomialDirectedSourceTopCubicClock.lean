import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceLowerToTopDissipationRatio
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceIntrinsicFrequencyCorridor

/-!
# Canonical terminal-kinetic sharp cubic clock for the genuine top H³ frequency

The canonical limiting kinetic coefficient C_* is already shown to satisfy

    q <= C_* (T-t)^2 (D/E)^3

on a sufficiently late physical tail under hypothetical nonextension, for
any fixed q<1. Independently, the intrinsic squared-frequency ratio

    (D3/E3)/(D/E) -> 1

on that same tail, without any nonlinear transport sign selection. Its cube
transfers the sharp subunit clock floor to the genuine top-order frequency:

    q <= C_* (T-t)^2 (D3/E3)^3  eventually, for every q<1.

An eventual or preselected-sequence subcritical ceiling for this TOP cubic
rate implies smooth continuation. These results retain the explicit
canonical H3 energy-data hypothesis required for C_*, and they preserve the
existing directed ten-source witness and both physical source alternatives.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Physical top-order cubic squared-frequency rate, with fourth-order
viscous dissipation divided by the third-order H³ energy. -/
noncomputable def h3PathCanonicalTopCubicRateAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : ℝ :=
  (T - t) ^ 2 *
    (velocityH3Dissipation3At u t / velocityH3Energy3At u t) ^ 3

/-- Canonically optimized top H³ cubic terminal clock. -/
noncomputable def h3PathCanonicalCanonicalTopCubicTerminalClockAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : ℝ :=
  h3PathCanonicalKineticLimitCubicCoefficient
      (h3PathCanonicalTerminalKineticEnergyAt u a T) *
    h3PathCanonicalTopCubicRateAt u T t

/-- Pointwise nonnegativity of the intrinsic top-order cubic rate. -/
theorem h3PathCanonical_topCubicRate_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) :
    0 ≤ h3PathCanonicalTopCubicRateAt u T t := by
  have hD : 0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg u t
  have hE : 0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg u t
  unfold h3PathCanonicalTopCubicRateAt
  exact mul_nonneg (sq_nonneg (T - t))
    (pow_nonneg (div_nonneg hD hE) 3)

/-- Exact full-to-top cubic rate identity wherever the top energy and full
dissipation denominators are positive. -/
theorem h3PathCanonical_topCubicRate_eq_fullRate_mul_intrinsicRatioCube
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hE3 : 0 < velocityH3Energy3At u t)
    (hD : 0 < velocityH3DissipationAt u t) :
    h3PathCanonicalTopCubicRateAt u T t =
      h3PathCanonicalFullCubicRateAt u T t *
        h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t ^ 3 := by
  have hE : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u t)
  unfold h3PathCanonicalTopCubicRateAt
    h3PathCanonicalFullCubicRateAt
    h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt
  field_simp [ne_of_gt hE3, ne_of_gt hD, ne_of_gt hE] <;> ring

/-- The terminal-kinetic limiting coefficient has sharp subunit lower
threshold also for the GENUINE top-order squared frequency D3/E3.
No exact eventual bound at q=1 is claimed. -/
theorem h3PathCanonical_canonicalTopCubicClock_eventually_ge_subunit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (q : ℝ) (hq : q < 1) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      q ≤ h3PathCanonicalCanonicalTopCubicTerminalClockAt u a T t := by
  let C : ℝ := h3PathCanonicalKineticLimitCubicCoefficient
    (h3PathCanonicalTerminalKineticEnergyAt u a T)
  have hC : 0 < C :=
    h3PathCanonical_kineticLimitCubicCoefficient_pos _
      (h3PathCanonical_terminalKineticEnergy_nonneg hClass)
  by_cases hqNonpos : q ≤ 0
  · exact Filter.Eventually.of_forall (fun t => by
      change q ≤ C * h3PathCanonicalTopCubicRateAt u T t
      exact hqNonpos.trans
        (mul_nonneg hC.le (h3PathCanonical_topCubicRate_nonneg u T t)))
  · have hqPos : 0 < q := lt_of_not_ge hqNonpos
    let r : ℝ := (q + 1) / 2
    have hrPos : 0 < r := by
      dsimp only [r]
      linarith only [hqPos]
    have hqr : q < r := by
      dsimp only [r]
      linarith only [hq]
    have hr : r < 1 := by
      dsimp only [r]
      linarith only [hq]
    have hFraction : q / r < 1 :=
      (div_lt_iff₀ hrPos).2 (by simpa only [one_mul] using hqr)
    have hFull : ∀ᶠ t : ℝ in 𝓝[<] T,
        r ≤ C * h3PathCanonicalFullCubicRateAt u T t := by
      simpa only [C] using
        (h3PathCanonical_canonicalKineticLimit_sharpCubicClock
          hH3 hNoExtension hClass hData r hr)
    have hb : h3BKMKineticTailMidpoint a T ∈ Set.Ioo a T :=
      h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
    have hRatio :=
      h3PathCanonical_intrinsicFrequencyRatio_tendsto_one_nhdsLT_of_noExtension
        hH3 hNoExtension hClass hb
    have hCube : Tendsto
        (fun t : ℝ =>
          h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t ^ 3)
        (𝓝[<] T) (𝓝 1) := by
      have hCont : ContinuousAt (fun x : ℝ => x ^ 3) 1 := by
        fun_prop
      simpa only [Function.comp_def, one_pow] using
        hCont.tendsto.comp hRatio
    have hRatioLarge : ∀ᶠ t : ℝ in 𝓝[<] T,
        q / r < h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t ^ 3 :=
      (tendsto_order.1 hCube).1 (q / r) hFraction
    have hE3T : Tendsto (velocityH3Energy3At u) (𝓝[<] T) atTop :=
      velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3 hNoExtension hClass
    have hD3T : Tendsto (velocityH3Dissipation3At u) (𝓝[<] T) atTop :=
      velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3 hNoExtension hClass
    have hE3Pos : ∀ᶠ t : ℝ in 𝓝[<] T,
        0 < velocityH3Energy3At u t := by
      filter_upwards [(tendsto_atTop.1 hE3T) 1] with t ht
      linarith only [ht]
    have hDPos : ∀ᶠ t : ℝ in 𝓝[<] T,
        0 < velocityH3DissipationAt u t := by
      filter_upwards [(tendsto_atTop.1 hD3T) 1] with t ht
      have hLe := h3PathCanonical_topDissipation_le_fullDissipation u t
      linarith only [ht, hLe]
    filter_upwards [hFull, hRatioLarge, hE3Pos, hDPos]
      with t hFullAt hRatioAt hE3At hDAt
    have hRatioPos : 0 < h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t ^ 3 :=
      lt_of_le_of_lt (div_nonneg hqPos.le hrPos.le) hRatioAt
    have hCompare := mul_le_mul_of_nonneg_right hFullAt hRatioPos.le
    have hStrict : q < r *
        h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t ^ 3 := by
      have hAux := (div_lt_iff₀ hrPos).1 hRatioAt
      simpa only [mul_comm] using hAux
    change q ≤ C * h3PathCanonicalTopCubicRateAt u T t
    calc
      q ≤ r * h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t ^ 3 :=
        le_of_lt hStrict
      _ ≤ (C * h3PathCanonicalFullCubicRateAt u T t) *
            h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t ^ 3 :=
        hCompare
      _ = C * h3PathCanonicalTopCubicRateAt u T t := by
        rw [h3PathCanonical_topCubicRate_eq_fullRate_mul_intrinsicRatioCube
          u T t hE3At hDAt]
        ring

/-- Eventual strict subcritical ceiling on the TOP frequency cubic rate
implies smooth continuation; the coefficient is optimized at the canonical
terminal kinetic energy rather than at any fixed kinetic anchor. -/
theorem h3PathCanonical_smoothExtension_of_canonicalTopCubicRateCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (hCeiling : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalTopCubicRateAt u T t ≤ B)
    (hStrict : h3PathCanonicalKineticLimitCubicCoefficient
        (h3PathCanonicalTerminalKineticEnergyAt u a T) * B < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  let C : ℝ := h3PathCanonicalKineticLimitCubicCoefficient
    (h3PathCanonicalTerminalKineticEnergyAt u a T)
  have hC : 0 ≤ C :=
    (h3PathCanonical_kineticLimitCubicCoefficient_pos _
      (h3PathCanonical_terminalKineticEnergy_nonneg hClass)).le
  let q : ℝ := (C * B + 1) / 2
  have hq : q < 1 := by
    dsimp only [q, C] at *
    linarith only [hStrict]
  have hGap : C * B < q := by
    dsimp only [q, C] at *
    linarith only [hStrict]
  have hFloor : ∀ᶠ t : ℝ in 𝓝[<] T,
      q ≤ h3PathCanonicalCanonicalTopCubicTerminalClockAt u a T t :=
    h3PathCanonical_canonicalTopCubicClock_eventually_ge_subunit
      hH3 hNoExtension hClass hData q hq
  have hUpper : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalCanonicalTopCubicTerminalClockAt u a T t ≤ C * B := by
    filter_upwards [hCeiling] with t ht
    change C * h3PathCanonicalTopCubicRateAt u T t ≤ C * B
    exact mul_le_mul_of_nonneg_left ht hC
  obtain ⟨t, hFloorAt, hUpperAt⟩ := (hFloor.and hUpper).exists
  exact (not_lt_of_ge (le_trans hFloorAt hUpperAt)) hGap

/-- The top cubic rate continuation test also holds along any already
selected sequence approaching T from below. -/
theorem h3PathCanonical_smoothExtension_of_sequence_canonicalTopCubicRateCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (tau : ℕ → ℝ)
    (hTau : Tendsto tau atTop (𝓝[<] T))
    (hCeiling : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalTopCubicRateAt u T (tau n) ≤ B)
    (hStrict : h3PathCanonicalKineticLimitCubicCoefficient
        (h3PathCanonicalTerminalKineticEnergyAt u a T) * B < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  let C : ℝ := h3PathCanonicalKineticLimitCubicCoefficient
    (h3PathCanonicalTerminalKineticEnergyAt u a T)
  have hC : 0 ≤ C :=
    (h3PathCanonical_kineticLimitCubicCoefficient_pos _
      (h3PathCanonical_terminalKineticEnergy_nonneg hClass)).le
  let q : ℝ := (C * B + 1) / 2
  have hq : q < 1 := by
    dsimp only [q, C] at *
    linarith only [hStrict]
  have hGap : C * B < q := by
    dsimp only [q, C] at *
    linarith only [hStrict]
  have hFloor : ∀ᶠ n : ℕ in atTop,
      q ≤ h3PathCanonicalCanonicalTopCubicTerminalClockAt u a T (tau n) :=
    hTau.eventually
      (h3PathCanonical_canonicalTopCubicClock_eventually_ge_subunit
        hH3 hNoExtension hClass hData q hq)
  have hUpper : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalCanonicalTopCubicTerminalClockAt u a T (tau n) ≤ C * B := by
    filter_upwards [hCeiling] with n hn
    change C * h3PathCanonicalTopCubicRateAt u T (tau n) ≤ C * B
    exact mul_le_mul_of_nonneg_left hn hC
  obtain ⟨n, hFloorAt, hUpperAt⟩ := (hFloor.and hUpper).exists
  exact (not_lt_of_ge (le_trans hFloorAt hUpperAt)) hGap

/-- The SAME fixed ten-source witness inherits the top-order sharp cubic
clock and retains both the lower/top viscous ratio limit and all previously
packaged physical alternative and fifth-clock results. -/
theorem h3PathCanonical_fixedDirectedSource_canonicalTopCubicClock_withPhysicalAlternative
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
        h3PathCanonicalTopDissipationFifthClockAt u T (tau n))
        atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalLowerToTopDissipationRatioAt u (tau n))
        atTop (𝓝 0) ∧
      (∀ q : ℝ, q < 1 →
        ∀ᶠ n : ℕ in atTop,
          q ≤ h3PathCanonicalCanonicalTopCubicTerminalClockAt u a T (tau n)) ∧
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
  obtain ⟨i, tau, hWitness, hTauT, hTopT,
    _hFullFifth, hTopFifth, _hFifthRatio, _hFifthDefect,
    _hLowerShare, hLowerTop, _hCorridor, _hSharp, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_lowerToTopDissipationRatio_withPhysicalAlternative
      hH3 hNoExtension hClass hData hb
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hTopSharp : ∀ q : ℝ, q < 1 →
      ∀ᶠ n : ℕ in atTop,
        q ≤ h3PathCanonicalCanonicalTopCubicTerminalClockAt u a T (tau n) := by
    intro q hq
    exact hTauLT.eventually
      (h3PathCanonical_canonicalTopCubicClock_eventually_ge_subunit
        hH3 hNoExtension hClass hData q hq)
  exact ⟨i, tau, hWitness, hTauT, hTopT, hTopFifth,
    hLowerTop, hTopSharp, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
