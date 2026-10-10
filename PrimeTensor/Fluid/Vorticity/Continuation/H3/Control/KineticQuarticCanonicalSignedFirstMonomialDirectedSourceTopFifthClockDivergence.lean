import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceFifthClockDivergence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceFullTailDissipationShare

/-!
# Full-tail fifth-power escape of the genuine fourth-order H³ dissipation

Previous results establish, conditionally on no smooth H³ extension and
canonical H³ energy data, the full physical dissipation rate

    (T-t)^5 D(t)^3 -> +infinity

along the entire left terminal neighborhood. The independent full-tail
concentration theorem gives D(t) ≤ (1+epsilon) D₃(t) eventually, without
an additional PDE transport sign. With epsilon=1 this yields the exact
pointwise comparison

    (T-t)^5 D(t)^3 ≤ 8 (T-t)^5 D₃(t)^3.

Thus the *top* fourth-derivative dissipation obeys the same critical fifth-
power cubic escape on the entire left tail. Eventual or sampled boundedness of
the top clock forces continuation. The original ten-source witness, including
its fixed index, critical clocks, and exhaustive gradient / signed-monomial
alternatives, is unchanged. These claims do not construct a singularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Physical terminal fifth-power clock of the true top viscous H³ block. -/
noncomputable def h3PathCanonicalTopDissipationFifthClockAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : ℝ :=
  (T - t) ^ 5 * velocityH3Dissipation3At u t ^ 3

/-- The full fifth-power clock is bounded by eight times the top clock
whenever full dissipation is bounded by twice the top block. -/
theorem h3PathCanonical_fullFifthClock_le_eight_topFifthClock
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (ht : t < T)
    (hD : velocityH3DissipationAt u t ≤
      2 * velocityH3Dissipation3At u t) :
    h3PathCanonicalFullDissipationFifthClockAt u T t ≤
      8 * h3PathCanonicalTopDissipationFifthClockAt u T t := by
  have hDNonneg : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hCube : velocityH3DissipationAt u t ^ 3 ≤
      (2 * velocityH3Dissipation3At u t) ^ 3 :=
    pow_le_pow_left₀ hDNonneg hD 3
  have hWidth : 0 ≤ (T - t) ^ 5 :=
    pow_nonneg (sub_nonneg.mpr (le_of_lt ht)) 5
  have hScale := mul_le_mul_of_nonneg_left hCube hWidth
  change (T - t) ^ 5 * velocityH3DissipationAt u t ^ 3 ≤
    8 * ((T - t) ^ 5 * velocityH3Dissipation3At u t ^ 3)
  calc
    (T - t) ^ 5 * velocityH3DissipationAt u t ^ 3 ≤
      (T - t) ^ 5 * (2 * velocityH3Dissipation3At u t) ^ 3 := hScale
    _ = 8 * ((T - t) ^ 5 * velocityH3Dissipation3At u t ^ 3) := by ring

/-- Hypothetical nonextension forces a uniform full-to-top comparison
for the fifth-power physical dissipation clock on a terminal subtail. -/
theorem h3PathCanonical_fullFifthClock_eventually_le_eight_topFifthClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalFullDissipationFifthClockAt u T t ≤
        8 * h3PathCanonicalTopDissipationFifthClockAt u T t := by
  have hb : h3BKMKineticTailMidpoint a T ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  have hDiss :=
    h3PathCanonical_eventually_fullDissipation_le_one_add_epsilon_top_nhdsLT
      hH3 hNoExtension hClass hb 1 (by norm_num)
  have hTail : Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2
  filter_upwards [hDiss, hTail] with t hD ht
  have hDouble : velocityH3DissipationAt u t ≤
      2 * velocityH3Dissipation3At u t := by
    convert hD using 1 <;> ring
  exact h3PathCanonical_fullFifthClock_le_eight_topFifthClock
    u T t ht.2 hDouble

/-- Under canonical kinetic data and hypothetical nonextension, the top
fourth-derivative viscous block obeys the entire-tail fifth-power escape:

    (T-t)^5 D₃(t)^3 -> +infinity.
-/
theorem h3PathCanonical_topDissipationFifthClock_tendsto_atTop_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T) :
    Tendsto (h3PathCanonicalTopDissipationFifthClockAt u T)
      (𝓝[<] T) atTop := by
  have hFull :=
    h3PathCanonical_fullDissipationFifthClock_tendsto_atTop_of_noExtension
      hH3 hNoExtension hClass hData
  have hComparison :=
    h3PathCanonical_fullFifthClock_eventually_le_eight_topFifthClock
      hH3 hNoExtension hClass
  refine tendsto_atTop.2 ?_
  intro M
  have hLarge : ∀ᶠ t : ℝ in 𝓝[<] T,
      8 * max M 0 ≤ h3PathCanonicalFullDissipationFifthClockAt u T t :=
    (tendsto_atTop.1 hFull) (8 * max M 0)
  filter_upwards [hLarge, hComparison] with t hLargeAt hCompareAt
  have hM : M ≤ max M 0 := le_max_left M 0
  linarith only [hLargeAt, hCompareAt, hM]

/-- An eventual finite top-order fifth-power clock ceiling excludes
nonextension, without a new transport-sign hypothesis. -/
theorem h3PathCanonical_smoothExtension_of_topFifthDissipationClock_ceiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (hCeiling : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalTopDissipationFifthClockAt u T t ≤ B) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hDiverges :=
    h3PathCanonical_topDissipationFifthClock_tendsto_atTop_of_noExtension
      hH3 hNoExtension hClass hData
  have hAbove : ∀ᶠ t : ℝ in 𝓝[<] T,
      B + 1 ≤ h3PathCanonicalTopDissipationFifthClockAt u T t :=
    hDiverges.eventually (eventually_ge_atTop (B + 1))
  obtain ⟨t, htAbove, htBelow⟩ := (hAbove.and hCeiling).exists
  linarith only [htAbove, htBelow]

/-- A bounded top-order fifth-power clock on any preselected terminal
sequence also yields smooth continuation. -/
theorem h3PathCanonical_smoothExtension_of_sequence_topFifthDissipationClock_ceiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (tau : ℕ → ℝ)
    (hTau : Tendsto tau atTop (𝓝[<] T))
    (hCeiling : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalTopDissipationFifthClockAt u T (tau n) ≤ B) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hDiverges :=
    (h3PathCanonical_topDissipationFifthClock_tendsto_atTop_of_noExtension
      hH3 hNoExtension hClass hData).comp hTau
  have hAbove : ∀ᶠ n : ℕ in atTop,
      B + 1 ≤ h3PathCanonicalTopDissipationFifthClockAt u T (tau n) :=
    hDiverges.eventually (eventually_ge_atTop (B + 1))
  obtain ⟨n, hnAbove, hnBelow⟩ := (hAbove.and hCeiling).exists
  linarith only [hnAbove, hnBelow]

/-- The same fixed ten-source witness exhibits both full and genuine
top-order fifth-power dissipation escape, with the canonical sharp clock,
three critical clocks, and exhaustive source alternatives unchanged. -/
theorem h3PathCanonical_fixedDirectedSource_topFifthDissipationClock_withPhysicalAlternative
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
      Tendsto (fun n : ℕ =>
        h3PathCanonicalFullDissipationFifthClockAt u T (tau n))
        atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalTopDissipationFifthClockAt u T (tau n))
        atTop atTop ∧
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
  obtain ⟨i, tau, hWitness, hTauT, hTopT, hLengthRatioT,
    hFifthFull, hSharp, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_fifthDissipationClock_withPhysicalAlternative
      hH3 hNoExtension hClass hData hb
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hFifthTop :=
    (h3PathCanonical_topDissipationFifthClock_tendsto_atTop_of_noExtension
      hH3 hNoExtension hClass hData).comp hTauLT
  exact ⟨i, tau, hWitness, hTauT, hTopT, hLengthRatioT,
    hFifthFull, hFifthTop, hSharp, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
