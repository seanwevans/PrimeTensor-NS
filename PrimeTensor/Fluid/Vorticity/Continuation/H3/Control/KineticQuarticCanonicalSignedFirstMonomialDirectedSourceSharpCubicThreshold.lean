import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceFullFrequencyCubicClock

/-!
# Sharp asymptotic full H³ cubic clock and recurrent-subcritical continuation

The previous physical frequency clock gives, for every epsilon > 0,

    1 <= (1+epsilon)^6 * C_b * (T-t)^2 * (D/E)^3

on the whole late terminal tail under hypothetical H³ nonextension, where
`C_b = 3 K^2 (E₀(b)+1)` is fixed by the kinetic anchor.

Letting the *coefficient tolerance* shrink (not assuming it is zero) shows
that the dimensionless physical clock is eventually above every q < 1.
Equivalently its terminal liminf is at least one, without falsely claiming
that the clock is eventually >= 1 for the exact coefficient.

Contrapositively, recurrent dips strictly below any fixed q < 1 force a
smooth continuation. The original fixed indexed directed ten-source witness
inherits the same sharp terminal threshold with both source branches intact.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Dimensionless full H³ cubic dissipation clock at a fixed kinetic anchor.
No epsilon-dependent coefficient is included in its definition. -/
noncomputable def h3PathCanonicalFullCubicTerminalClockAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t : ℝ) : ℝ :=
  (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1)) * (T - t) ^ 2 *
    (velocityH3DissipationAt u t / velocityH3EnergyAt u t) ^ 3

/-- For any strict subunit threshold q, an explicitly positive epsilon
can be chosen so that q * (1+epsilon)^6 < 1. -/
theorem h3PathCanonical_exists_positive_cubicTolerance
    (q : ℝ) (hq : q < 1) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ q * (1 + epsilon) ^ 6 < 1 := by
  have hCont : ContinuousAt (fun epsilon : ℝ =>
      q * (1 + epsilon) ^ 6) 0 := by
    fun_prop
  have hZero : q * (1 + (0 : ℝ)) ^ 6 < 1 := by
    simpa only [add_zero, one_pow, mul_one] using hq
  have hNear : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      q * (1 + epsilon) ^ 6 < 1 := by
    have hLimit :
        Tendsto (fun epsilon : ℝ => q * (1 + epsilon) ^ 6)
          (𝓝[>] (0 : ℝ)) (𝓝 (q * (1 + (0 : ℝ)) ^ 6)) :=
      hCont.tendsto.mono_left
        (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    exact hLimit.eventually (Iio_mem_nhds hZero)
  have hPositive : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      0 < epsilon := self_mem_nhdsWithin
  obtain ⟨epsilon, hEpsilon, hBound⟩ := (hPositive.and hNear).exists
  exact ⟨epsilon, hEpsilon, hBound⟩

/-- The exact anchored cubic clock has asymptotic lower threshold one:
for every q < 1 it is at least q throughout a late left-terminal interval.
This does NOT assert eventual `1 <= clock` without the tolerance. -/
theorem h3PathCanonical_fullCubicTerminalClock_eventually_ge_subunit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (q : ℝ) (hq : q < 1) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      q ≤ h3PathCanonicalFullCubicTerminalClockAt u T b t := by
  obtain ⟨epsilon, hEpsilon, hTol⟩ :=
    h3PathCanonical_exists_positive_cubicTolerance q hq
  have hA : 0 < (1 + epsilon) ^ 6 := by
    have hOne : 0 < 1 + epsilon := by linarith only [hEpsilon]
    positivity
  have hQ : q < 1 / (1 + epsilon) ^ 6 :=
    (lt_div_iff₀ hA).2 hTol
  have hRate :=
    h3PathCanonical_fullPhysicalDissipationCubic_terminalClock_eventually
      hH3 hNoExtension hClass hb epsilon hEpsilon
  filter_upwards [hRate] with t ht
  have hClock : 1 / (1 + epsilon) ^ 6 ≤
      h3PathCanonicalFullCubicTerminalClockAt u T b t := by
    apply (div_le_iff₀ hA).2
    calc
      1 ≤ ((1 + epsilon) ^ 6 *
          (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            (velocityH3Energy0At u b + 1)) * (T - t) ^ 2) *
          (velocityH3DissipationAt u t / velocityH3EnergyAt u t) ^ 3 := ht
      _ = h3PathCanonicalFullCubicTerminalClockAt u T b t *
          (1 + epsilon) ^ 6 := by
        unfold h3PathCanonicalFullCubicTerminalClockAt
        ring
  exact (le_of_lt hQ).trans hClock

/-- Recurrent strictly subcritical cubic-clock values, arbitrarily late
on the physical time interval, exclude a nonextendible H³ path. The
subcritical threshold can be any fixed q < 1. -/
theorem h3PathCanonical_smoothExtension_of_recurrent_subunit_cubicClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (q : ℝ) (hq : q < 1)
    (hRecurrent : ∀ c : ℝ, c ∈ Set.Ioo b T →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        h3PathCanonicalFullCubicTerminalClockAt u T b t < q) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hFloor := h3PathCanonical_fullCubicTerminalClock_eventually_ge_subunit
    hH3 hNoExtension hClass hb q hq
  obtain ⟨c, hcT, hSub⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset).mp hFloor
  let m : ℝ := (b + T) / 2
  have hm : m ∈ Set.Ioo b T := by
    dsimp only [m]
    constructor <;> linarith only [hb.2]
  let d : ℝ := max m c
  have hd : d ∈ Set.Ioo b T := by
    constructor
    · exact lt_of_lt_of_le hm.1 (le_max_left m c)
    · exact max_lt hm.2 hcT
  obtain ⟨t, ht, hSmall⟩ := hRecurrent d hd
  have hct : c < t := lt_of_le_of_lt (le_max_right m c) ht.1
  have hLarge : q ≤ h3PathCanonicalFullCubicTerminalClockAt u T b t :=
    hSub ⟨hct, ht.2⟩
  exact (not_lt_of_ge hLarge) hSmall

/-- The SAME fixed directed ten-source sequence inherits the sharp full
cubic-clock threshold for every q < 1, as well as its original fixed index,
three physical critical clocks and neutral adverse-source alternatives. -/
theorem h3PathCanonical_fixedDirectedSource_sharpCubicClock_withPhysicalAlternative
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
        h3PathCanonicalFullToTopPhysicalLengthRatioAt u (tau n))
        atTop (𝓝 1) ∧
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
  obtain ⟨i, tau, hWitness, hTauT, hTopT, _hEnergyShare,
    _hSquaredRatio, _hFrequencyRatio, _hTopLengthT, _hFullLengthT,
    hLengthRatioT, _hLengthRate, _hIndexedFloor, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_fullDissipationCubicIndexed_withPhysicalAlternative
      hH3 hNoExtension hClass hb 1 (by norm_num)
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hSharp : ∀ q : ℝ, q < 1 →
      ∀ᶠ n : ℕ in atTop,
        q ≤ h3PathCanonicalFullCubicTerminalClockAt u T b (tau n) := by
    intro q hq
    exact hTauLT.eventually
      (h3PathCanonical_fullCubicTerminalClock_eventually_ge_subunit
        hH3 hNoExtension hClass hb q hq)
  exact ⟨i, tau, hWitness, hTauT, hTopT, hLengthRatioT,
    hSharp, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
