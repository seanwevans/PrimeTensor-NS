import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxWeightedDissipationContinuationGate
import Mathlib.Tactic

/-!
# Three-halves terminal weight from the actual cubic H3 dissipation rate

The accepted nonextension implication is the physical cubic rate

  1 <= B * (T-t)^8 * D3(t)^3.

The previous inverse-square theorem spent two powers of terminal distance
and gave nonintegrability of (T-t)*D_full. Squaring the ORIGINAL cubic
inequality and choosing a later tail where B^2*(T-t) <= 1 yields

  1 <= (T-t)^5 * D3(t)^2.

With d=T-t>0 this implies 1/d <= d*sqrt(d)*D3(t), hence
nonintegrability of (T-t)*sqrt(T-t)*D_full on every terminal subtail
under nonextension. Its finiteness on one strict subtail forces smooth
continuation. This is the weight d^(3/2), strictly beyond the linear weight.

This does not assert that any Navier--Stokes trajectory satisfies the
weighted-integrability premise. The critical d^(5/3) scale is not asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Squaring the physical cubic rate retains an extra half power of the
terminal distance, provided its fixed coefficient is small on that tail. -/
theorem thirdFullKinetic_scalar_cubicRate_forces_quinticSquare244
    (B d D : ℝ) (hd : 0 < d) (hD : 0 ≤ D)
    (hSmall : B ^ 2 * d ≤ 1)
    (hRate : 1 ≤ B * d ^ 8 * D ^ 3) :
    1 ≤ d ^ 5 * D ^ 2 := by
  have hRateSquared : 1 ≤ (B * d ^ 8 * D ^ 3) ^ 2 := by
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hRate 2
    simpa only [one_pow] using hs
  have hZ0 : 0 ≤ d ^ 5 * D ^ 2 :=
    mul_nonneg (pow_nonneg hd.le 5) (sq_nonneg D)
  by_contra hn
  have hLt : d ^ 5 * D ^ 2 < 1 := lt_of_not_ge hn
  have hCube : (d ^ 5 * D ^ 2) ^ 3 < 1 := by
    have hPower := pow_lt_pow_left₀ hLt hZ0 (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [one_pow] using hPower
  have hCube0 : 0 ≤ (d ^ 5 * D ^ 2) ^ 3 := pow_nonneg hZ0 3
  have hUpper : (B ^ 2 * d) * (d ^ 5 * D ^ 2) ^ 3 < 1 := by
    calc
      (B ^ 2 * d) * (d ^ 5 * D ^ 2) ^ 3 ≤
          1 * (d ^ 5 * D ^ 2) ^ 3 :=
        mul_le_mul_of_nonneg_right hSmall hCube0
      _ < 1 * 1 := mul_lt_mul_of_pos_left hCube (by norm_num)
      _ = 1 := by norm_num
  have hFactor : (B * d ^ 8 * D ^ 3) ^ 2 =
      (B ^ 2 * d) * (d ^ 5 * D ^ 2) ^ 3 := by ring
  rw [hFactor] at hRateSquared
  exact (not_lt_of_ge hRateSquared) hUpper

/-- The nonnegative square root of the scalar quintic rate gives exactly
the harmonic lower bound for the three-halves weighted dissipation. -/
theorem thirdFullKinetic_scalar_quinticSquare_harmonicSqrtWeight244
    (d D : ℝ) (hd : 0 < d) (hD : 0 ≤ D)
    (hQuintic : 1 ≤ d ^ 5 * D ^ 2) :
    1 / d ≤ d * Real.sqrt d * D := by
  have hRootSq : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd.le
  have hW0 : 0 ≤ d ^ 2 * Real.sqrt d * D := by positivity
  have hWsq : (d ^ 2 * Real.sqrt d * D) ^ 2 = d ^ 5 * D ^ 2 := by
    calc
      (d ^ 2 * Real.sqrt d * D) ^ 2 =
          d ^ 4 * (Real.sqrt d) ^ 2 * D ^ 2 := by ring
      _ = d ^ 5 * D ^ 2 := by rw [hRootSq]; ring
  have hSq : (1 : ℝ) ^ 2 ≤ (d ^ 2 * Real.sqrt d * D) ^ 2 := by
    simpa only [one_pow, hWsq] using hQuintic
  have hLinear : 1 ≤ d ^ 2 * Real.sqrt d * D :=
    (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hW0).mp hSq
  apply (div_le_iff₀ hd).mpr
  calc
    1 ≤ d ^ 2 * Real.sqrt d * D := hLinear
    _ = (d * Real.sqrt d * D) * d := by ring

/-- Nonextension forces the true full H3 physical dissipation to have a
nonintegrable d^(3/2) weighted harmonic floor on a strict terminal tail. -/
theorem thirdFullPhysical_noExtension_harmonicThreeHalvesDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ, c ∈ Set.Ioo b T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T →
        1 / (T - t) ≤
          (T - t) * Real.sqrt (T - t) * velocityH3DissipationAt u t := by
  obtain ⟨cRate, hcRate, hRate⟩ :=
    exists_terminalTail_topH3DissipationRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  let B : ℝ := 81 * h3PathSqrtEnergyRiccatiCoefficient ^ 8 *
    velocityH3Energy0At u b
  let C : ℝ := B ^ 2
  obtain ⟨cSmall, hcSmall, hSmall⟩ :=
    exists_terminalTail_const_mul_terminalDistance_sq_le_one
      (C ^ 2) T b hb.2
  let c : ℝ := max cRate cSmall
  have hc : c ∈ Set.Ioo b T := by
    constructor
    · exact lt_of_lt_of_le hcRate.1 (le_max_left cRate cSmall)
    · exact max_lt hcRate.2 hcSmall.2
  refine ⟨c, hc, ?_⟩
  intro t ht
  have htRate : t ∈ Set.Ioo cRate T :=
    ⟨lt_of_le_of_lt (show cRate ≤ c from le_max_left _ _) ht.1, ht.2⟩
  have htSmall : t ∈ Set.Ioo cSmall T :=
    ⟨lt_of_le_of_lt (show cSmall ≤ c from le_max_right _ _) ht.1, ht.2⟩
  let d : ℝ := T - t
  let D : ℝ := velocityH3Dissipation3At u t
  have hd : 0 < d := sub_pos.mpr ht.2
  have hD : 0 ≤ D := velocityH3Dissipation3At_nonneg u t
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hCSmall : C ^ 2 * d ^ 2 ≤ 1 := by
    simpa only [d] using hSmall t htSmall
  have hCDsq : (C * d) ^ 2 ≤ (1 : ℝ) ^ 2 := by
    calc
      (C * d) ^ 2 = C ^ 2 * d ^ 2 := by ring
      _ ≤ 1 := hCSmall
      _ = (1 : ℝ) ^ 2 := by norm_num
  have hCD : C * d ≤ 1 :=
    (sq_le_sq₀ (mul_nonneg hC0 hd.le)
      (by norm_num : (0 : ℝ) ≤ 1)).mp hCDsq
  have hBSmall : B ^ 2 * d ≤ 1 := by
    simpa only [C] using hCD
  have hRateB : 1 ≤ B * d ^ 8 * D ^ 3 := by
    calc
      1 ≤ 81 * h3PathSqrtEnergyRiccatiCoefficient ^ 8 *
          (T - t) ^ 8 * velocityH3Energy0At u b *
          velocityH3Dissipation3At u t ^ 3 := hRate t htRate
      _ = B * d ^ 8 * D ^ 3 := by dsimp only [B, d, D]; ring
  have hQuintic : 1 ≤ d ^ 5 * D ^ 2 :=
    thirdFullKinetic_scalar_cubicRate_forces_quinticSquare244
      B d D hd hD hBSmall hRateB
  have hTop : 1 / d ≤ d * Real.sqrt d * D :=
    thirdFullKinetic_scalar_quinticSquare_harmonicSqrtWeight244
      d D hd hD hQuintic
  have hPhysical : D ≤ velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt u t
  have hFactor : 0 ≤ d * Real.sqrt d :=
    mul_nonneg hd.le (Real.sqrt_nonneg d)
  have hScale : d * Real.sqrt d * D ≤
      d * Real.sqrt d * velocityH3DissipationAt u t := by
    exact mul_le_mul_of_nonneg_left hPhysical hFactor
  exact hTop.trans (by simpa only [d, D] using hScale)

/-- The physical three-halves weighted full-H3 dissipation cannot be
integrable on any strict terminal subtail of a nonextendible path. -/
theorem thirdFullPhysical_noExtension_threeHalvesDissipation_nonintegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ¬ MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) * Real.sqrt (T - t) *
        velocityH3DissipationAt u t) (Set.Ioo b T) := by
  obtain ⟨c, hc, hLower⟩ :=
    thirdFullPhysical_noExtension_harmonicThreeHalvesDissipation244
      hH3 hNoExtension hClass b hb
  intro hWeighted
  have hTail : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) * Real.sqrt (T - t) *
        velocityH3DissipationAt u t) (Set.Ioo c T) := by
    apply hWeighted.mono_set
    intro t ht
    exact ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hReciprocal : MeasureTheory.IntegrableOn
      (fun t : ℝ => 1 / (T - t)) (Set.Ioo c T) := by
    apply Integrable.mono' hTail
    · exact (show Measurable (fun t : ℝ => 1 / (T - t)) by
        fun_prop).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hd : 0 < T - t := sub_pos.mpr ht.2
      have hWeightNonneg : 0 ≤ (T - t) * Real.sqrt (T - t) *
          velocityH3DissipationAt u t := by
        exact mul_nonneg
          (mul_nonneg hd.le (Real.sqrt_nonneg _))
          (velocityH3DissipationAt_nonneg u t)
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hd)]
      simpa only [Real.norm_eq_abs, abs_of_nonneg hWeightNonneg] using
        hLower t ht
  exact not_integrableOn_one_div_terminalDistance hc.2 hReciprocal

/-- Finiteness of the d^(3/2)-weighted full-H3 physical dissipation on
one strict subtail forces smooth continuation through the terminal time. -/
theorem thirdFullPhysical_threeHalvesDissipation_strictTail_forcesContinuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hWeighted : IntervalIntegrable
      (fun t : ℝ => (T - t) * Real.sqrt (T - t) *
        velocityH3DissipationAt u t) volume b T) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  classical
  by_contra hNoExtension
  have hForbidden :=
    thirdFullPhysical_noExtension_threeHalvesDissipation_nonintegrable244
      hH3 hNoExtension hClass b hb
  apply hForbidden
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).mp
    hWeighted

/-- The d^(3/2)-weighted continuation criterion on the original H3
energy-class terminal interval. -/
theorem thirdFullPhysical_threeHalvesDissipation_energyTail_forcesContinuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hWeighted : IntervalIntegrable
      (fun t : ℝ => (T - t) * Real.sqrt (T - t) *
        velocityH3DissipationAt u t) volume a T) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  let b : ℝ := h3BKMKineticTailMidpoint a T
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  have hFull : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) * Real.sqrt (T - t) *
        velocityH3DissipationAt u t) (Set.Ioo a T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      hClass.terminal_start.2.le).mp hWeighted
  have hTail : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) * Real.sqrt (T - t) *
        velocityH3DissipationAt u t) (Set.Ioo b T) := by
    apply hFull.mono_set
    intro t ht
    exact ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hTailInt : IntervalIntegrable
      (fun t : ℝ => (T - t) * Real.sqrt (T - t) *
        velocityH3DissipationAt u t) volume b T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).mpr hTail
  exact thirdFullPhysical_threeHalvesDissipation_strictTail_forcesContinuation244
    hH3 hClass b hb hTailInt

end
end PrimeTensor.FirstMonomialTriad
