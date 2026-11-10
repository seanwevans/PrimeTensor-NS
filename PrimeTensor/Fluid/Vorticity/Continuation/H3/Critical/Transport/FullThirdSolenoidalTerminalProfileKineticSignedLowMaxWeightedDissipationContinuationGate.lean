import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxFiniteDissipationContinuationGate
import Mathlib.Tactic

/-!
# Weighted full-H3 dissipation: an inverse-square terminal obstruction

The preceding finite-full-H3-dissipation continuation theorem used only the
harmonic lower bound D3(t) >= 1/(T-t) in the hypothetical nonextension branch.
The *earlier cubic terminal rate* actually yields the stronger inverse-square
floor. Its proof requires no cube roots or new PDE axioms:

    1 <= B (T-t)^8 D3(t)^3,
    B (T-t)^2 <= 1
    ==> 1 <= (T-t)^2 D3(t).

Therefore, eventually,

    1/(T-t) <= (T-t) D_full(t).

The right side is not integrable on any terminal strict subtail under
hypothetical nonextension. Consequently the additional hypothesis

    IntervalIntegrable (fun t => (T-t) * D_full(t)) volume b T

on even ONE strict terminal subtail implies smooth continuation through T.
Unlike unweighted finite dissipation, the weight T-t vanishes at the
terminal point. This is a strictly weaker conditional analytic criterion,
not a proof that arbitrary 3D Navier--Stokes solutions satisfy it.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The precise scalar cubic rate-to-square mechanism. A terminal coefficient
that becomes small at the quadratic distance scale forces the full
inverse-square dissipation cost. The proof works even when B is not
explicitly assumed nonnegative. -/
theorem thirdFullKinetic_scalar_cubicRate_forces_inverseSquare244
    (B d D : ℝ) (hD : 0 ≤ D)
    (hSmall : B * d ^ 2 ≤ 1)
    (hRate : 1 ≤ B * d ^ 8 * D ^ 3) :
    1 ≤ d ^ 2 * D := by
  have hProductNonneg : 0 ≤ d ^ 2 * D :=
    mul_nonneg (sq_nonneg d) hD
  by_contra hn
  have hLt : d ^ 2 * D < 1 := lt_of_not_ge hn
  have hCubeLtRaw : (d ^ 2 * D) ^ 3 < (1 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hLt hProductNonneg (by norm_num)
  have hCubeLt : (d ^ 2 * D) ^ 3 < 1 := by
    simpa using hCubeLtRaw
  have hCubeNonneg : 0 ≤ (d ^ 2 * D) ^ 3 :=
    pow_nonneg hProductNonneg 3
  have hContr : B * d ^ 2 * (d ^ 2 * D) ^ 3 < 1 := by
    calc
      B * d ^ 2 * (d ^ 2 * D) ^ 3 ≤
          1 * (d ^ 2 * D) ^ 3 :=
        mul_le_mul_of_nonneg_right hSmall hCubeNonneg
      _ < 1 * 1 := mul_lt_mul_of_pos_left hCubeLt (by norm_num)
      _ = 1 := by norm_num
  have hFactor :
      B * d ^ 8 * D ^ 3 = B * d ^ 2 * (d ^ 2 * D) ^ 3 := by
    ring
  rw [hFactor] at hRate
  exact (not_lt_of_ge hRate) hContr

/-- Under hypothetical nonextension, the actual FULL physical dissipation
has an inverse-square lower bound on a nonempty strict terminal subtail.
This recovers the square-scale inequality left unused by the older harmonic
proof and then uses the established physical D3 <= D_full comparison. -/
theorem thirdFullPhysical_noExtension_inverseSquareFullDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ, c ∈ Set.Ioo b T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T →
        1 ≤ (T - t) ^ 2 * velocityH3DissipationAt u t := by
  obtain ⟨cRate, hcRate, hRate⟩ :=
    exists_terminalTail_topH3DissipationRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  let B : ℝ := 81 * h3PathSqrtEnergyRiccatiCoefficient ^ 8 *
    velocityH3Energy0At u b
  let M : ℝ := max B 1
  obtain ⟨cSmall, hcSmall, hSmall⟩ :=
    exists_terminalTail_const_mul_terminalDistance_sq_le_one M T b hb.2
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
  have hSmallM : M * d ^ 2 ≤ 1 := hSmall t htSmall
  have hBLeM : B ≤ M := le_max_left B 1
  have hSmallB : B * d ^ 2 ≤ 1 :=
    (mul_le_mul_of_nonneg_right hBLeM (sq_nonneg d)).trans hSmallM
  have hRateB : 1 ≤ B * d ^ 8 * D ^ 3 := by
    calc
      1 ≤ 81 * h3PathSqrtEnergyRiccatiCoefficient ^ 8 *
          (T - t) ^ 8 * velocityH3Energy0At u b *
          velocityH3Dissipation3At u t ^ 3 := hRate t htRate
      _ = B * d ^ 8 * D ^ 3 := by dsimp only [B, d, D]; ring
  have hD0 : 0 ≤ D := velocityH3Dissipation3At_nonneg u t
  have hD3Square : 1 ≤ d ^ 2 * D :=
    thirdFullKinetic_scalar_cubicRate_forces_inverseSquare244
      B d D hD0 hSmallB hRateB
  have hFull : D ≤ velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt u t
  have hScale : d ^ 2 * D ≤ d ^ 2 * velocityH3DissipationAt u t :=
    mul_le_mul_of_nonneg_left hFull (sq_nonneg d)
  exact hD3Square.trans (by simpa only [d, D] using hScale)

/-- The critical terminal weight d=T-t converts the inverse-square
physical dissipation lower bound into the nonintegrable harmonic density. -/
theorem thirdFullPhysical_noExtension_harmonicWeightedFullDissipation244
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
          (T - t) * velocityH3DissipationAt u t := by
  obtain ⟨c, hc, hSquare⟩ :=
    thirdFullPhysical_noExtension_inverseSquareFullDissipation244
      hH3 hNoExtension hClass b hb
  refine ⟨c, hc, ?_⟩
  intro t ht
  have hd : 0 < T - t := sub_pos.mpr ht.2
  apply (div_le_iff₀ hd).2
  calc
    1 ≤ (T - t) ^ 2 * velocityH3DissipationAt u t := hSquare t ht
    _ = ((T - t) * velocityH3DissipationAt u t) * (T - t) := by ring

/-- The linearly weighted full-H3 viscous cost is nonintegrable on EVERY
strict terminal tail in the hypothetical nonextension branch. -/
theorem thirdFullPhysical_noExtension_weightedFullDissipation_nonintegrableStrictTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => (T - t) * velocityH3DissipationAt u t)
        (Set.Ioo b T) := by
  obtain ⟨c, hc, hLower⟩ :=
    thirdFullPhysical_noExtension_harmonicWeightedFullDissipation244
      hH3 hNoExtension hClass b hb
  intro hWeighted
  have hTail : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) * velocityH3DissipationAt u t)
      (Set.Ioo c T) := by
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
      have hWeightedNonneg :
          0 ≤ (T - t) * velocityH3DissipationAt u t :=
        mul_nonneg hd.le (velocityH3DissipationAt_nonneg u t)
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hd)]
      simpa only [Real.norm_eq_abs, abs_of_nonneg hWeightedNonneg] using
        hLower t ht
  exact not_integrableOn_one_div_terminalDistance hc.2 hReciprocal

/-- FINITENESS of just the linearly time-weighted full-H3 dissipation on
ONE strict terminal subtail forces smooth continuation. No bound on
unweighted full dissipation is assumed. -/
theorem thirdFullPhysical_weightedFullDissipation_strictTail_forcesContinuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hWeighted : IntervalIntegrable
      (fun t : ℝ => (T - t) * velocityH3DissipationAt u t)
      volume b T) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  classical
  by_contra hNoExtension
  have hForbidden :=
    thirdFullPhysical_noExtension_weightedFullDissipation_nonintegrableStrictTail244
      hH3 hNoExtension hClass b hb
  apply hForbidden
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).mp
    hWeighted

/-- The corresponding weighted criterion on the original energy-class
terminal interval; the proof restricts the integral to a strict subtail. -/
theorem thirdFullPhysical_weightedFullDissipation_energyTail_forcesContinuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hWeighted : IntervalIntegrable
      (fun t : ℝ => (T - t) * velocityH3DissipationAt u t)
      volume a T) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  let b : ℝ := h3BKMKineticTailMidpoint a T
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  have hFull : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) * velocityH3DissipationAt u t)
      (Set.Ioo a T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      hClass.terminal_start.2.le).mp hWeighted
  have hTail : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) * velocityH3DissipationAt u t)
      (Set.Ioo b T) := by
    apply hFull.mono_set
    intro t ht
    exact ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hTailInt : IntervalIntegrable
      (fun t : ℝ => (T - t) * velocityH3DissipationAt u t)
      volume b T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).mpr hTail
  exact thirdFullPhysical_weightedFullDissipation_strictTail_forcesContinuation244
    hH3 hClass b hb hTailInt

end
end PrimeTensor.FirstMonomialTriad
