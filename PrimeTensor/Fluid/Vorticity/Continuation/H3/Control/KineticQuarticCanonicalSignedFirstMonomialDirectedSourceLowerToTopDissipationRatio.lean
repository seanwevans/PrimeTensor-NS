import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceLowerDissipationRecurrence

/-!
# Lower-to-top physical H³ viscous dissipation ratio

The preceding physical lower-block fraction theorem proves that
`(D₀+D₁+D₂)/D -> 0` on the full terminal tail under hypothetical
nonextension. A sharper comparison uses the genuine top fourth-order block
as denominator. The existing fixed-epsilon spectral concentration theorem
states, for each ε>0, eventually

    D₀(t)+D₁(t)+D₂(t) <= ε D₃(t).

Since D₃(t) -> +infinity along the entire left terminal neighborhood, its
positive denominator yields

    (D₀(t)+D₁(t)+D₂(t))/D₃(t) -> 0.

A fixed positive lower-to-top viscous ratio recurring arbitrarily close to
T, or persisting along a preselected left-terminal sequence, forces smooth
continuation. These theorems need the preterminal H³ energy class but not an
additional canonical kinetic-energy-data hypothesis. The fixed directed
source witness inherits the ratio limit alongside both fifth-power clocks
and the neutral gradient/ordered signed-monomial alternative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Full lower viscous energy normalized by the genuine top-order viscous
block, rather than by the full dissipation. -/
noncomputable def h3PathCanonicalLowerToTopDissipationRatioAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  h3PathCanonicalLowerDissipationAt u t / velocityH3Dissipation3At u t

/-- The lower-to-top physical viscous ratio is nonnegative at every time,
with real division's zero-denominator convention. -/
theorem h3PathCanonical_lowerToTopDissipationRatio_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3PathCanonicalLowerToTopDissipationRatioAt u t := by
  have h0 := velocityH3Dissipation0At_nonneg u t
  have h1 := velocityH3Dissipation1At_nonneg u t
  have h2 := velocityH3Dissipation2At_nonneg u t
  have hLow : 0 ≤ h3PathCanonicalLowerDissipationAt u t := by
    unfold h3PathCanonicalLowerDissipationAt
    linarith only [h0, h1, h2]
  unfold h3PathCanonicalLowerToTopDissipationRatioAt
  exact div_nonneg hLow (velocityH3Dissipation3At_nonneg u t)

/-- Complete left-terminal concentration of all viscous H³ dissipation in
the top fourth-order block, now normalized by that block itself. This is a
stronger denominator normalization than the preceding `lower/D -> 0`. -/
theorem h3PathCanonical_lowerToTopDissipationRatio_tendsto_zero_nhdsLT_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    Tendsto (h3PathCanonicalLowerToTopDissipationRatioAt u)
      (𝓝[<] T) (𝓝 0) := by
  have hTop :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hTopOne : ∀ᶠ t : ℝ in 𝓝[<] T,
      1 ≤ velocityH3Dissipation3At u t :=
    (tendsto_atTop.1 hTop) 1
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    exact Filter.Eventually.of_forall (fun t =>
      lt_of_lt_of_le hc (h3PathCanonical_lowerToTopDissipationRatio_nonneg u t))
  · intro c hc
    have hEpsilon : 0 < c / 2 := by linarith only [hc]
    have hLower :=
      h3PathCanonical_eventually_lowerDissipation_le_epsilon_top_nhdsLT
        hH3 hNoExtension hClass hb (c / 2) hEpsilon
    filter_upwards [hLower, hTopOne] with t hLowBound hD3One
    have hD3Pos : 0 < velocityH3Dissipation3At u t :=
      lt_of_lt_of_le zero_lt_one hD3One
    have hQuotient : h3PathCanonicalLowerToTopDissipationRatioAt u t ≤ c / 2 := by
      unfold h3PathCanonicalLowerToTopDissipationRatioAt
      apply (div_le_iff₀ hD3Pos).2
      simpa only [h3PathCanonicalLowerDissipationAt] using hLowBound
    exact lt_of_le_of_lt hQuotient (by linarith only [hc])

/-- Every positive tolerance eventually controls the *true* lower-to-top
viscous ratio, uniformly throughout the strict physical left terminal tail. -/
theorem h3PathCanonical_lowerToTopDissipationRatio_eventually_lt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalLowerToTopDissipationRatioAt u t < epsilon := by
  exact (tendsto_order.1
    (h3PathCanonical_lowerToTopDissipationRatio_tendsto_zero_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb)).2 epsilon hEpsilon

/-- A fixed positive lower-to-top dissipative contribution on arbitrarily
late strict subtails contradicts nonextension. No canonical energy data or
sign selection for the nonlinear transport is needed. -/
theorem h3PathCanonical_smoothExtension_of_recurrent_positiveLowerToTopDissipationRatio
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b delta : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hDelta : 0 < delta)
    (hRecurrent : ∀ c : ℝ, c ∈ Set.Ioo b T →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        delta ≤ h3PathCanonicalLowerToTopDissipationRatioAt u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hSmall :=
    h3PathCanonical_lowerToTopDissipationRatio_eventually_lt
      hH3 hNoExtension hClass hb delta hDelta
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
  obtain ⟨t, ht, hPositive⟩ := hRecurrent d hd
  have hct : c < t := lt_of_le_of_lt (le_max_right m c) ht.1
  have hSmallAt : h3PathCanonicalLowerToTopDissipationRatioAt u t < delta :=
    hSub ⟨hct, ht.2⟩
  exact (not_lt_of_ge hPositive) hSmallAt

/-- Positive lower/top ratio persisting along any preselected left-terminal
sequence is sufficient for smooth H³ continuation. -/
theorem h3PathCanonical_smoothExtension_of_sequence_positiveLowerToTopDissipationRatio
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b delta : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (tau : ℕ → ℝ)
    (hTau : Tendsto tau atTop (𝓝[<] T))
    (hDelta : 0 < delta)
    (hPersistent : ∀ᶠ n : ℕ in atTop,
      delta ≤ h3PathCanonicalLowerToTopDissipationRatioAt u (tau n)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hSmall : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalLowerToTopDissipationRatioAt u (tau n) < delta :=
    hTau.eventually
      (h3PathCanonical_lowerToTopDissipationRatio_eventually_lt
        hH3 hNoExtension hClass hb delta hDelta)
  obtain ⟨n, hnSmall, hnPersistent⟩ := (hSmall.and hPersistent).exists
  exact (not_lt_of_ge hnPersistent) hnSmall

/-- The SAME fixed ten-source witness retains all previously established
fifth-clock, relative-concentration, kinetic-floor, and critical-clock
conclusions, and additionally has lower/top viscous ratio tending to zero.
The combined package retains canonical energy data because fifth-power
clock divergence requires them; the preceding ratio limit does not. -/
theorem h3PathCanonical_fixedDirectedSource_lowerToTopDissipationRatio_withPhysicalAlternative
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
      Tendsto (fun n : ℕ =>
        h3PathCanonicalLowerDissipationFractionAt u (tau n))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalLowerToTopDissipationRatioAt u (tau n))
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
    hRatio, hDefect, hLowShare, hCorridor, hSharp, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_lowerDissipationFraction_withPhysicalAlternative
      hH3 hNoExtension hClass hData hb
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hLowTop :=
    (h3PathCanonical_lowerToTopDissipationRatio_tendsto_zero_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb).comp hTauLT
  exact ⟨i, tau, hWitness, hTauT, hTopT,
    hFullFifth, hTopFifth, hRatio, hDefect, hLowShare, hLowTop,
    hCorridor, hSharp, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
