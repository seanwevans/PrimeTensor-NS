import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceTopFifthClockDivergence

/-!
# Exact relative equivalence of the two physical H³ fifth-power clocks

The earlier conditional results establish two individually diverging
terminal dissipation clocks, `(T-t)^5 D(t)^3` and `(T-t)^5 D₃(t)^3`.
Their exact quotient is `(D₃/D)^3` whenever `t<T` and `D(t)>0`.
The independent full-tail concentration result `D₃/D -> 1` thus implies

  (top fifth clock)/(full fifth clock) -> 1

on the ENTIRE physical left terminal neighborhood. The corresponding
relative defect tends to zero. For every positive tolerance, the top clock
is eventually strictly above `(1-epsilon)` times the full clock, and is
always at most the full clock at preterminal times. Both alternatives of
the original fixed directed ten-source witness are retained without an
additional Navier--Stokes sign assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Ratio of fourth-order and full physical fifth-power viscous clocks. -/
noncomputable def h3PathCanonicalTopToFullFifthClockRatioAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : ℝ :=
  h3PathCanonicalTopDissipationFifthClockAt u T t /
    h3PathCanonicalFullDissipationFifthClockAt u T t

/-- The full-clock-relative lower-block defect, which is not claimed
absolutely small: only its *fraction of the full fifth clock* vanishes. -/
noncomputable def h3PathCanonicalFifthClockRelativeDefectAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : ℝ :=
  1 - h3PathCanonicalTopToFullFifthClockRatioAt u T t

/-- The time-width powers cancel exactly from the quotient of the two
fifth-power clocks, whenever the full dissipation is positive. -/
theorem h3PathCanonical_fifthClockRatio_eq_dissipationShare_cube
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (ht : t < T)
    (hD : 0 < velocityH3DissipationAt u t) :
    h3PathCanonicalTopToFullFifthClockRatioAt u T t =
      (velocityH3Dissipation3At u t /
        velocityH3DissipationAt u t) ^ 3 := by
  have hWidth : T - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have hDNe : velocityH3DissipationAt u t ≠ 0 := ne_of_gt hD
  unfold h3PathCanonicalTopToFullFifthClockRatioAt
    h3PathCanonicalTopDissipationFifthClockAt
    h3PathCanonicalFullDissipationFifthClockAt
  field_simp [hWidth, hDNe] <;> ring

/-- In a hypothetical nonextendible H³ path the top and full physical
fifth-power dissipation clocks are relatively equivalent throughout the
COMPLETE left terminal neighborhood, not merely on selected times. -/
theorem h3PathCanonical_fifthClockRatio_tendsto_one_nhdsLT_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    Tendsto (h3PathCanonicalTopToFullFifthClockRatioAt u T)
      (𝓝[<] T) (𝓝 1) := by
  have hShare :=
    h3PathCanonical_dissipationTopShare_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hPow : Tendsto (fun t : ℝ =>
      (velocityH3Dissipation3At u t /
        velocityH3DissipationAt u t) ^ 3)
      (𝓝[<] T) (𝓝 (1 : ℝ)) := by
    have hCont : ContinuousAt (fun x : ℝ => x ^ 3) 1 := by
      fun_prop
    simpa only [Function.comp_def, one_pow] using
      hCont.tendsto.comp hShare
  have hD3T : Tendsto (velocityH3Dissipation3At u)
      (𝓝[<] T) atTop :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hD3One : ∀ᶠ t : ℝ in 𝓝[<] T,
      1 ≤ velocityH3Dissipation3At u t :=
    (tendsto_atTop.1 hD3T) 1
  have hTail : Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2
  have hEq : (fun t : ℝ =>
      (velocityH3Dissipation3At u t /
        velocityH3DissipationAt u t) ^ 3) =ᶠ[𝓝[<] T]
      h3PathCanonicalTopToFullFifthClockRatioAt u T := by
    filter_upwards [hD3One, hTail] with t hD3 ht
    have hD : 0 < velocityH3DissipationAt u t :=
      lt_of_lt_of_le zero_lt_one
        (le_trans hD3 (h3PathCanonical_topDissipation_le_fullDissipation u t))
    exact (h3PathCanonical_fifthClockRatio_eq_dissipationShare_cube
      u T t ht.2 hD).symm
  exact hPow.congr' hEq

/-- The normalized lower-block fifth-clock remainder vanishes, even
though its UNnormalized value need not be bounded or approach zero. -/
theorem h3PathCanonical_fifthClockRelativeDefect_tendsto_zero_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    Tendsto (h3PathCanonicalFifthClockRelativeDefectAt u T)
      (𝓝[<] T) (𝓝 0) := by
  have hRatio :=
    h3PathCanonical_fifthClockRatio_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hCont : ContinuousAt (fun x : ℝ => 1 - x) 1 := by
    fun_prop
  change Tendsto
    (fun t : ℝ => 1 - h3PathCanonicalTopToFullFifthClockRatioAt u T t)
      (𝓝[<] T) (𝓝 0)
  simpa only [Function.comp_def, sub_self] using
    hCont.tendsto.comp hRatio

/-- Regardless of terminal hypotheses, on preterminal times the top
fifth-power dissipation clock cannot exceed the full fifth clock. -/
theorem h3PathCanonical_topFifthClock_le_fullFifthClock
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) (ht : t < T) :
    h3PathCanonicalTopDissipationFifthClockAt u T t ≤
      h3PathCanonicalFullDissipationFifthClockAt u T t := by
  have hD3Nonneg : 0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg u t
  have hD3Le := h3PathCanonical_topDissipation_le_fullDissipation u t
  have hCube := pow_le_pow_left₀ hD3Nonneg hD3Le 3
  have hWidth : 0 ≤ (T - t) ^ 5 :=
    pow_nonneg (sub_nonneg.mpr (le_of_lt ht)) 5
  unfold h3PathCanonicalTopDissipationFifthClockAt
    h3PathCanonicalFullDissipationFifthClockAt
  exact mul_le_mul_of_nonneg_left hCube hWidth

/-- The relative fifth-clock equivalence yields a genuinely physical
strict lower comparison with arbitrarily small multiplicative loss.
The reverse inequality is exact, without any multiplicative loss. -/
theorem h3PathCanonical_fifthClocks_eventually_strictRelativeCorridor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b epsilon : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hEpsilon : 0 < epsilon) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      (1 - epsilon) * h3PathCanonicalFullDissipationFifthClockAt u T t <
        h3PathCanonicalTopDissipationFifthClockAt u T t ∧
      h3PathCanonicalTopDissipationFifthClockAt u T t ≤
        h3PathCanonicalFullDissipationFifthClockAt u T t := by
  have hRatio :=
    h3PathCanonical_fifthClockRatio_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hLower : 1 - epsilon < (1 : ℝ) := by
    linarith only [hEpsilon]
  have hCorridor : ∀ᶠ t : ℝ in 𝓝[<] T,
      1 - epsilon < h3PathCanonicalTopToFullFifthClockRatioAt u T t :=
    (tendsto_order.1 hRatio).1 (1 - epsilon) hLower
  have hD3T : Tendsto (velocityH3Dissipation3At u)
      (𝓝[<] T) atTop :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hD3One : ∀ᶠ t : ℝ in 𝓝[<] T,
      1 ≤ velocityH3Dissipation3At u t :=
    (tendsto_atTop.1 hD3T) 1
  have hTail : Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2
  filter_upwards [hCorridor, hD3One, hTail] with t hLo hD3 ht
  have hD : 0 < velocityH3DissipationAt u t :=
    lt_of_lt_of_le zero_lt_one
      (le_trans hD3 (h3PathCanonical_topDissipation_le_fullDissipation u t))
  have hFullPos : 0 < h3PathCanonicalFullDissipationFifthClockAt u T t := by
    unfold h3PathCanonicalFullDissipationFifthClockAt
    exact mul_pos (pow_pos (sub_pos.mpr ht.2) 5) (pow_pos hD 3)
  constructor
  · exact (lt_div_iff₀ hFullPos).mp hLo
  · exact h3PathCanonical_topFifthClock_le_fullFifthClock u T t ht.2

/-- The SAME indexed source sequence retains the joint full/top fifth-clock
escape and their asymptotically identical physical values, together with
the sharp kinetic clock, critical clocks, and both signed-source branches. -/
theorem h3PathCanonical_fixedDirectedSource_fifthClockEquivalence_withPhysicalAlternative
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
        h3PathCanonicalFullDissipationFifthClockAt u T (tau n))
        atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalTopDissipationFifthClockAt u T (tau n))
        atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalTopToFullFifthClockRatioAt u T (tau n))
        atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalFifthClockRelativeDefectAt u T (tau n))
        atTop (𝓝 0) ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ n : ℕ in atTop,
          (1 - epsilon) *
              h3PathCanonicalFullDissipationFifthClockAt u T (tau n) <
                h3PathCanonicalTopDissipationFifthClockAt u T (tau n) ∧
          h3PathCanonicalTopDissipationFifthClockAt u T (tau n) ≤
            h3PathCanonicalFullDissipationFifthClockAt u T (tau n)) ∧
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
  obtain ⟨i, tau, hWitness, hTauT, hTopT, _hLengthRatio,
    hFullFifth, hTopFifth, hSharp, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_topFifthDissipationClock_withPhysicalAlternative
      hH3 hNoExtension hClass hData hb
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hRatio :=
    (h3PathCanonical_fifthClockRatio_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb).comp hTauLT
  have hDefect :=
    (h3PathCanonical_fifthClockRelativeDefect_tendsto_zero_nhdsLT
      hH3 hNoExtension hClass hb).comp hTauLT
  have hCorridor : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        (1 - epsilon) *
            h3PathCanonicalFullDissipationFifthClockAt u T (tau n) <
              h3PathCanonicalTopDissipationFifthClockAt u T (tau n) ∧
        h3PathCanonicalTopDissipationFifthClockAt u T (tau n) ≤
          h3PathCanonicalFullDissipationFifthClockAt u T (tau n) := by
    intro epsilon hEpsilon
    exact hTauLT.eventually
      (h3PathCanonical_fifthClocks_eventually_strictRelativeCorridor
        hH3 hNoExtension hClass hb hEpsilon)
  exact ⟨i, tau, hWitness, hTauT, hTopT,
    hFullFifth, hTopFifth, hRatio, hDefect, hCorridor,
    hSharp, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
