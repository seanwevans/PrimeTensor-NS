import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceTopCubicClock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.Eventual

/-!
# Eighth-power interpolation floor and fifth-power escape without canonical H³ data

The old Fourier fourth-moment argument already proves, with only the logged
preterminal path and the H³ energy class, that for every fixed kinetic anchor
`b` and every sufficiently late physical time,

  1 ≤ 81 K⁸ E₀(b) (T-t)⁸ D₃(t)³.

Multiplying a hypothetical *bounded* fifth-power clock `(T-t)⁵ D₃³`
by `(T-t)³ → 0` contradicts this floor. Hence under nonextension the
top fifth clock diverges on the entire physical left terminal filter,
without `CanonicalH3EnergyDataOnTail`. The full fifth clock dominates it.

The resulting two continuation tests and the original fixed directed-source
witness likewise need no extra canonical analytic-energy-data hypothesis.
No sign of either PDE source alternative is selected, and no actual blowup
or unconditional regularity statement is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Eighth-power physical top viscous clock (without the fixed anchor factor). -/
noncomputable def h3PathCanonicalTopDissipationEighthClockAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : ℝ :=
  (T - t) ^ 8 * velocityH3Dissipation3At u t ^ 3

/-- The established interpolation and inverse-square top-energy estimate
supply an eighth-power floor on a whole terminal subtail. In particular,
this theorem does NOT need the additional canonical H³ energy data. -/
theorem h3PathCanonical_topEighthClock_eventually_anchoredFloor_noCanonicalData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      1 ≤ (81 * h3PathSqrtEnergyRiccatiCoefficient ^ 8 *
          velocityH3Energy0At u b) *
        h3PathCanonicalTopDissipationEighthClockAt u T t := by
  obtain ⟨c, hc, hRate⟩ :=
    exists_terminalTail_topH3DissipationRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  have hTail : Set.Ioo c T ∈ 𝓝[<] T := Ioo_mem_nhdsLT hc.2
  filter_upwards [hTail] with t ht
  calc
    1 ≤ 81 * h3PathSqrtEnergyRiccatiCoefficient ^ 8 *
        (T - t) ^ 8 * velocityH3Energy0At u b *
          velocityH3Dissipation3At u t ^ 3 := hRate t ht
    _ = (81 * h3PathSqrtEnergyRiccatiCoefficient ^ 8 *
          velocityH3Energy0At u b) *
        h3PathCanonicalTopDissipationEighthClockAt u T t := by
      unfold h3PathCanonicalTopDissipationEighthClockAt
      ring

/-- The eighth-clock floor forces the top fifth-power dissipation clock
to diverge throughout the whole left-terminal filter. A hypothetical finite
fifth-clock ceiling would make the eighth clock vanish. -/
theorem h3PathCanonical_topFifthClock_tendsto_atTop_noCanonicalData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto (h3PathCanonicalTopDissipationFifthClockAt u T)
      (𝓝[<] T) atTop := by
  let b : ℝ := h3BKMKineticTailMidpoint a T
  have hb : b ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  let A : ℝ := 81 * h3PathSqrtEnergyRiccatiCoefficient ^ 8 *
    velocityH3Energy0At u b
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hE0 := velocityH3Energy0At_nonneg u b
    positivity
  have hFloor : ∀ᶠ t : ℝ in 𝓝[<] T,
      1 ≤ A * h3PathCanonicalTopDissipationEighthClockAt u T t := by
    simpa only [A] using
      (h3PathCanonical_topEighthClock_eventually_anchoredFloor_noCanonicalData
        hH3 hNoExtension hClass hb)
  refine tendsto_atTop.2 ?_
  intro M
  have hCont : ContinuousAt
      (fun t : ℝ => A * (T - t) ^ 3 * max M 0) T := by
    fun_prop
  have hSmallLimit : Tendsto
      (fun t : ℝ => A * (T - t) ^ 3 * max M 0)
      (𝓝[<] T) (𝓝 0) := by
    have h := hCont.tendsto.mono_left
      (show (𝓝[<] T) ≤ 𝓝 T from nhdsWithin_le_nhds)
    simpa using h
  have hSmall : ∀ᶠ t : ℝ in 𝓝[<] T,
      A * (T - t) ^ 3 * max M 0 < 1 :=
    (tendsto_order.1 hSmallLimit).2 1 (by norm_num)
  have hTail : Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2
  filter_upwards [hFloor, hSmall, hTail] with t hFloorAt hSmallAt ht
  have hGap : 0 ≤ T - t := sub_nonneg.mpr (le_of_lt ht.2)
  have hScale : 0 ≤ A * (T - t) ^ 3 :=
    mul_nonneg hA (pow_nonneg hGap 3)
  have hFloorFifth :
      1 ≤ (A * (T - t) ^ 3) *
        h3PathCanonicalTopDissipationFifthClockAt u T t := by
    calc
      1 ≤ A * h3PathCanonicalTopDissipationEighthClockAt u T t := hFloorAt
      _ = (A * (T - t) ^ 3) *
          h3PathCanonicalTopDissipationFifthClockAt u T t := by
        unfold h3PathCanonicalTopDissipationEighthClockAt
          h3PathCanonicalTopDissipationFifthClockAt
        ring
  by_contra hNot
  have hLess : h3PathCanonicalTopDissipationFifthClockAt u T t < M :=
    lt_of_not_ge hNot
  have hUp : h3PathCanonicalTopDissipationFifthClockAt u T t ≤ max M 0 :=
    (le_of_lt hLess).trans (le_max_left M 0)
  have hContradiction : (1 : ℝ) < 1 := by
    calc
      1 ≤ (A * (T - t) ^ 3) *
          h3PathCanonicalTopDissipationFifthClockAt u T t := hFloorFifth
      _ ≤ (A * (T - t) ^ 3) * max M 0 :=
        mul_le_mul_of_nonneg_left hUp hScale
      _ < 1 := hSmallAt
  exact (lt_irrefl (1 : ℝ)) hContradiction

/-- Full fifth-power dissipation escape follows from the top escape and
the pointwise inequality `D₃≤D`, without canonical analytic energy data. -/
theorem h3PathCanonical_fullFifthClock_tendsto_atTop_noCanonicalData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto (h3PathCanonicalFullDissipationFifthClockAt u T)
      (𝓝[<] T) atTop := by
  have hTop :=
    h3PathCanonical_topFifthClock_tendsto_atTop_noCanonicalData
      hH3 hNoExtension hClass
  have hTail : Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2
  refine tendsto_atTop.2 ?_
  intro M
  have hHigh : ∀ᶠ t : ℝ in 𝓝[<] T,
      M ≤ h3PathCanonicalTopDissipationFifthClockAt u T t :=
    (tendsto_atTop.1 hTop) M
  filter_upwards [hHigh, hTail] with t ht htTail
  exact ht.trans (h3PathCanonical_topFifthClock_le_fullFifthClock u T t htTail.2)

/-- A bounded top-order physical fifth clock forces continuation with just
the logged admissible H³ path and preterminal energy class. -/
theorem h3PathCanonical_smoothExtension_of_topFifthClock_ceiling_noCanonicalData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hCeiling : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalTopDissipationFifthClockAt u T t ≤ B) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hEscape := h3PathCanonical_topFifthClock_tendsto_atTop_noCanonicalData
    hH3 hNoExtension hClass
  have hHigh : ∀ᶠ t : ℝ in 𝓝[<] T,
      B + 1 ≤ h3PathCanonicalTopDissipationFifthClockAt u T t :=
    hEscape.eventually (eventually_ge_atTop (B + 1))
  obtain ⟨t, htHigh, htLow⟩ := (hHigh.and hCeiling).exists
  linarith only [htHigh, htLow]

/-- Even a finite top-order fifth-clock ceiling on a preselected terminal
sequence forces continuation without extra canonical kinetic data. -/
theorem h3PathCanonical_smoothExtension_of_sequence_topFifthClock_ceiling_noCanonicalData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (tau : ℕ → ℝ)
    (hTau : Tendsto tau atTop (𝓝[<] T))
    (hCeiling : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalTopDissipationFifthClockAt u T (tau n) ≤ B) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hEscape :=
    (h3PathCanonical_topFifthClock_tendsto_atTop_noCanonicalData
      hH3 hNoExtension hClass).comp hTau
  have hHigh : ∀ᶠ n : ℕ in atTop,
      B + 1 ≤ h3PathCanonicalTopDissipationFifthClockAt u T (tau n) :=
    hEscape.eventually (eventually_ge_atTop (B + 1))
  obtain ⟨n, hnHigh, hnLow⟩ := (hHigh.and hCeiling).exists
  linarith only [hnHigh, hnLow]

/-- The original fixed directed ten-source witness inherits BOTH fifth-clock
escapes without canonical analytic data. Its full physical cubic floor,
critical clocks and exhaustive nonlinear gradient/signed-source alternatives
remain the same; no new sequence or source index is selected. -/
theorem h3PathCanonical_fixedDirectedSource_fifthClocks_noCanonicalData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
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
        h3PathCanonicalTopDissipationFifthClockAt u T (tau n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalFullDissipationFifthClockAt u T (tau n)) atTop atTop ∧
      (∀ q : ℝ, q < 1 →
        ∀ᶠ n : ℕ in atTop,
          q ≤ h3PathCanonicalFullCubicTerminalClockAt u T b (tau n)) ∧
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
    hSharp, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_sharpCubicClock_withPhysicalAlternative
      hH3 hNoExtension hClass hb
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hTopFifth :=
    (h3PathCanonical_topFifthClock_tendsto_atTop_noCanonicalData
      hH3 hNoExtension hClass).comp hTauLT
  have hFullFifth :=
    (h3PathCanonical_fullFifthClock_tendsto_atTop_noCanonicalData
      hH3 hNoExtension hClass).comp hTauLT
  exact ⟨i, tau, hWitness, hTauT, hTopT,
    hTopFifth, hFullFifth, hSharp, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
