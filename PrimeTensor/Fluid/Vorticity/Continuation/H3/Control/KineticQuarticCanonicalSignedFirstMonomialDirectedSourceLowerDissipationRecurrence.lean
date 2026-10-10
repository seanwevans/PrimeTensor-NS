import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceFifthClockEquivalence

/-!
# Lower-order viscous dissipation: vanishing share and recurrent-obstruction continuation

The complete left-terminal dissipation-concentration theorem already gives,
conditionally on hypothetical nonextension, `D₃/D -> 1`. The exact physical
identity `D = D₀+D₁+D₂+D₃` therefore yields

  (D₀+D₁+D₂)/D -> 0

on the ENTIRE terminal left neighborhood. This conclusion does not require
`CanonicalH3EnergyDataOnTail`, unlike the fifth-power divergence results.

Consequently, if a fixed positive fraction of dissipation remains in the
three lower blocks arbitrarily late in time, smooth continuation follows.
The same holds for any preselected left-terminal sequence with a persistent
positive lower-block fraction. No nonlinear transport-sign choice is made.

The original ten-source witness additionally inherits the lower fraction's
zero limit, with both fifth-power clock escapes, its kinetic cubic threshold,
three critical clocks, and the neutral source alternatives unchanged (the
latter joint statement retains canonical energy data from the parent).
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Sum of the three lower-order physical viscous H³ blocks. -/
noncomputable def h3PathCanonicalLowerDissipationAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  velocityH3Dissipation0At u t + velocityH3Dissipation1At u t +
    velocityH3Dissipation2At u t

/-- The fraction of full viscous dissipation carried by lower-order blocks.
It is defined by real division at all times; positivity of D is established
on the terminal tail when the quotient is used analytically. -/
noncomputable def h3PathCanonicalLowerDissipationFractionAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  h3PathCanonicalLowerDissipationAt u t / velocityH3DissipationAt u t

/-- Exact lower/top viscous decomposition, independent of terminal data. -/
theorem h3PathCanonical_fullDissipation_eq_lower_add_top
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    velocityH3DissipationAt u t =
      h3PathCanonicalLowerDissipationAt u t + velocityH3Dissipation3At u t := by
  unfold h3PathCanonicalLowerDissipationAt velocityH3DissipationAt
  ring

/-- The lower viscous fraction is exactly the complement of the top
viscous share whenever full dissipation is positive. -/
theorem h3PathCanonical_lowerDissipationFraction_eq_one_sub_topShare
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hD : 0 < velocityH3DissipationAt u t) :
    h3PathCanonicalLowerDissipationFractionAt u t =
      1 - velocityH3Dissipation3At u t / velocityH3DissipationAt u t := by
  have hExact := h3PathCanonical_fullDissipation_eq_lower_add_top u t
  unfold h3PathCanonicalLowerDissipationFractionAt
  field_simp [ne_of_gt hD]
  linarith only [hExact]

/-- Hypothetical nonextension makes the three lower viscous blocks a
vanishing fraction of total dissipation on the COMPLETE terminal tail.
Crucially, no extra canonical kinetic-energy data are needed. -/
theorem h3PathCanonical_lowerDissipationFraction_tendsto_zero_nhdsLT_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    Tendsto (h3PathCanonicalLowerDissipationFractionAt u)
      (𝓝[<] T) (𝓝 0) := by
  have hTopShare :=
    h3PathCanonical_dissipationTopShare_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hCont : ContinuousAt (fun x : ℝ => 1 - x) 1 := by
    fun_prop
  have hComplement : Tendsto
      (fun t : ℝ => 1 -
        velocityH3Dissipation3At u t / velocityH3DissipationAt u t)
      (𝓝[<] T) (𝓝 0) := by
    simpa only [Function.comp_def, sub_self] using
      hCont.tendsto.comp hTopShare
  have hD3T : Tendsto (velocityH3Dissipation3At u)
      (𝓝[<] T) atTop :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hD3One : ∀ᶠ t : ℝ in 𝓝[<] T,
      1 ≤ velocityH3Dissipation3At u t :=
    (tendsto_atTop.1 hD3T) 1
  have hEquality :
      (fun t : ℝ => 1 -
        velocityH3Dissipation3At u t / velocityH3DissipationAt u t)
      =ᶠ[𝓝[<] T] h3PathCanonicalLowerDissipationFractionAt u := by
    filter_upwards [hD3One] with t hOne
    have hD : 0 < velocityH3DissipationAt u t :=
      lt_of_lt_of_le zero_lt_one
        (le_trans hOne (h3PathCanonical_topDissipation_le_fullDissipation u t))
    exact (h3PathCanonical_lowerDissipationFraction_eq_one_sub_topShare
      u t hD).symm
  exact hComplement.congr' hEquality

/-- A fixed positive lower-order dissipation fraction repeatedly appearing
arbitrarily close to T rules out hypothetical nonextension. This is a
cofinal/recurrent test, not a requirement of eventual boundedness. -/
theorem h3PathCanonical_smoothExtension_of_recurrent_positiveLowerDissipationFraction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b delta : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hDelta : 0 < delta)
    (hRecurrent : ∀ c : ℝ, c ∈ Set.Ioo b T →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        delta ≤ h3PathCanonicalLowerDissipationFractionAt u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hLimit :=
    h3PathCanonical_lowerDissipationFraction_tendsto_zero_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hSmall : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalLowerDissipationFractionAt u t < delta :=
    (tendsto_order.1 hLimit).2 delta hDelta
  obtain ⟨c, hcT, hSub⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset).mp hSmall
  let m : ℝ := (b + T) / 2
  have hm : m ∈ Set.Ioo b T := by
    dsimp only [m]
    constructor <;> linarith only [hb.2]
  let d : ℝ := max m c
  have hd : d ∈ Set.Ioo b T := by
    constructor
    · exact lt_of_lt_of_le hm.1 (le_max_left m c)
    · exact max_lt hm.2 hcT
  obtain ⟨t, ht, hPositiveFraction⟩ := hRecurrent d hd
  have hct : c < t := lt_of_le_of_lt (le_max_right m c) ht.1
  have hSmallAt : h3PathCanonicalLowerDissipationFractionAt u t < delta :=
    hSub ⟨hct, ht.2⟩
  exact (not_lt_of_ge hPositiveFraction) hSmallAt

/-- A persistent positive lower viscous fraction even along one preselected
left-terminal sequence forces smooth continuation. -/
theorem h3PathCanonical_smoothExtension_of_sequence_positiveLowerDissipationFraction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b delta : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (tau : ℕ → ℝ)
    (hTau : Tendsto tau atTop (𝓝[<] T))
    (hDelta : 0 < delta)
    (hPersistent : ∀ᶠ n : ℕ in atTop,
      delta ≤ h3PathCanonicalLowerDissipationFractionAt u (tau n)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hLimit :=
    h3PathCanonical_lowerDissipationFraction_tendsto_zero_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hSmall : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalLowerDissipationFractionAt u (tau n) < delta :=
    hTau.eventually ((tendsto_order.1 hLimit).2 delta hDelta)
  obtain ⟨n, hnSmall, hnPersistent⟩ := (hSmall.and hPersistent).exists
  exact (not_lt_of_ge hnPersistent) hnSmall

/-- The SAME fixed ten-source obstruction witness has vanishing lower
viscous fraction, retaining both fifth-clock escapes, their ratio/defect
limits, sharp terminal kinetic clock, critical physical clocks and both
nonlinear source alternatives. -/
theorem h3PathCanonical_fixedDirectedSource_lowerDissipationFraction_withPhysicalAlternative
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
        h3PathCanonicalFullDissipationFifthClockAt u T (tau n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalTopDissipationFifthClockAt u T (tau n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalTopToFullFifthClockRatioAt u T (tau n))
        atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalFifthClockRelativeDefectAt u T (tau n))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalLowerDissipationFractionAt u (tau n))
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
  obtain ⟨i, tau, hWitness, hTauT, hTopT, hFullFifth, hTopFifth,
    hRatio, hDefect, hCorridor, hSharp, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_fifthClockEquivalence_withPhysicalAlternative
      hH3 hNoExtension hClass hData hb
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hLow :=
    (h3PathCanonical_lowerDissipationFraction_tendsto_zero_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb).comp hTauLT
  exact ⟨i, tau, hWitness, hTauT, hTopT, hFullFifth, hTopFifth,
    hRatio, hDefect, hLow, hCorridor, hSharp, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
