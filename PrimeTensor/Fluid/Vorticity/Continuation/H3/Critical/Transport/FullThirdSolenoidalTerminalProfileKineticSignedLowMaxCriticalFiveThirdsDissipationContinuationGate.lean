import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxThreeHalvesDissipationContinuationGate
import Mathlib.Tactic

/-!
# Critical five-thirds weighted H3 continuation from the cubic terminal rate

The preceding three-halves continuation theorem sacrifices part of the
terminal scaling. Here the exact nonextension rate

  1 <= B * (T-t)^8 * D3(t)^3

is factored into a cube with exponent 8/3 and a fixed positive coefficient
C = max B 1. This yields the endpoint harmonic floor

  1/(T-t) <= C * (T-t)^(5/3) * D_full(t).

Unlike the three-halves proof, there is no small-tail coefficient argument:
B is carried through as a time-independent factor. Consequently, under
nonextension, the critically weighted physical dissipation is nonintegrable
on every strict terminal subtail. Integrability on one such subtail forces
smooth continuation, conditional on the existing admissibility and energy
class assumptions. No assertion of unconditional Navier--Stokes regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Exact scalar endpoint: the cubic rate forces a harmonic lower bound
with the fixed coefficient max B 1. No terminal-smallness hypothesis. -/
theorem thirdFullKinetic_scalar_cubicRate_harmonicCriticalFiveThirds244
    (B d D : ℝ) (hd : 0 < d) (hD : 0 ≤ D)
    (hRate : 1 ≤ B * d ^ 8 * D ^ 3) :
    1 / d ≤ (max B 1) * (d ^ ((5 : ℝ) / 3) * D) := by
  let C : ℝ := max B 1
  have hC1 : (1 : ℝ) ≤ C := le_max_right B 1
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hC2 : (1 : ℝ) ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - 1)]
  have hBCube : B ≤ C ^ 3 := by
    calc
      B ≤ C := le_max_left B 1
      _ = C * 1 := by ring
      _ ≤ C * C ^ 2 := mul_le_mul_of_nonneg_left hC2 hC0
      _ = C ^ 3 := by ring
  have hFactor0 : 0 ≤ d ^ 8 * D ^ 3 := by positivity
  have hPowEight :
      (d ^ ((8 : ℝ) / 3)) ^ (3 : ℕ) = d ^ (8 : ℕ) := by
    calc
      (d ^ ((8 : ℝ) / 3)) ^ (3 : ℕ) =
          (d ^ ((8 : ℝ) / 3)) ^ (3 : ℝ) :=
        (Real.rpow_natCast (d ^ ((8 : ℝ) / 3)) 3).symm
      _ = d ^ (((8 : ℝ) / 3) * 3) :=
        (Real.rpow_mul hd.le ((8 : ℝ) / 3) (3 : ℝ)).symm
      _ = d ^ (8 : ℝ) := by congr 1; ring
      _ = d ^ (8 : ℕ) := Real.rpow_natCast d 8
  let q : ℝ := C * (d ^ ((8 : ℝ) / 3)) * D
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hqCube : q ^ 3 = C ^ 3 * d ^ 8 * D ^ 3 := by
    dsimp only [q]
    rw [mul_pow, mul_pow, hPowEight] <;> ring
  have hqCubed : 1 ≤ q ^ 3 := by
    rw [hqCube]
    calc
      1 ≤ B * (d ^ 8 * D ^ 3) := by
        simpa only [mul_assoc] using hRate
      _ ≤ C ^ 3 * (d ^ 8 * D ^ 3) :=
        mul_le_mul_of_nonneg_right hBCube hFactor0
      _ = C ^ 3 * d ^ 8 * D ^ 3 := by ring
  have hqLinear : 1 ≤ q := by
    by_contra hn
    have hlt : q < 1 := lt_of_not_ge hn
    have hCubeLt : q ^ 3 < (1 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hlt hq0 (by norm_num : (3 : ℕ) ≠ 0)
    exact (not_lt_of_ge hqCubed) (by simpa using hCubeLt)
  have hSplit :
      d ^ ((8 : ℝ) / 3) = d * d ^ ((5 : ℝ) / 3) := by
    calc
      d ^ ((8 : ℝ) / 3) = d ^ ((1 : ℝ) + (5 : ℝ) / 3) := by
        congr 1
        ring
      _ = d ^ (1 : ℝ) * d ^ ((5 : ℝ) / 3) :=
        Real.rpow_add hd (1 : ℝ) ((5 : ℝ) / 3)
      _ = d * d ^ ((5 : ℝ) / 3) := by rw [Real.rpow_one]
  apply (div_le_iff₀ hd).mpr
  calc
    1 ≤ q := hqLinear
    _ = ((max B 1) * (d ^ ((5 : ℝ) / 3) * D)) * d := by
      dsimp only [q, C]
      rw [hSplit]
      ring

/-- Hypothetical nonextension forces the physical full-H3 dissipation
above a constant multiple of the exact five-thirds harmonic profile. -/
theorem thirdFullPhysical_noExtension_harmonicCriticalFiveThirdsDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ∃ C : ℝ, 0 < C ∧
      ∃ c : ℝ, c ∈ Set.Ioo b T ∧
        ∀ t : ℝ, t ∈ Set.Ioo c T →
          1 / (T - t) ≤
            C * ((T - t) ^ ((5 : ℝ) / 3) *
              velocityH3DissipationAt u t) := by
  obtain ⟨c, hc, hRate⟩ :=
    exists_terminalTail_topH3DissipationRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  let B : ℝ := 81 * h3PathSqrtEnergyRiccatiCoefficient ^ 8 *
    velocityH3Energy0At u b
  let C : ℝ := max B 1
  have hCpos : 0 < C :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (le_max_right B 1)
  refine ⟨C, hCpos, c, hc, ?_⟩
  intro t ht
  let d : ℝ := T - t
  let D : ℝ := velocityH3Dissipation3At u t
  have hd : 0 < d := sub_pos.mpr ht.2
  have hD : 0 ≤ D := velocityH3Dissipation3At_nonneg u t
  have hRateB : 1 ≤ B * d ^ 8 * D ^ 3 := by
    calc
      1 ≤ 81 * h3PathSqrtEnergyRiccatiCoefficient ^ 8 *
          (T - t) ^ 8 * velocityH3Energy0At u b *
          velocityH3Dissipation3At u t ^ 3 := hRate t ht
      _ = B * d ^ 8 * D ^ 3 := by dsimp only [B, d, D]; ring
  have hTop : 1 / d ≤ C * (d ^ ((5 : ℝ) / 3) * D) :=
    thirdFullKinetic_scalar_cubicRate_harmonicCriticalFiveThirds244
      B d D hd hD hRateB
  have hPhysical : D ≤ velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt u t
  have hFactor : 0 ≤ d ^ ((5 : ℝ) / 3) :=
    Real.rpow_nonneg hd.le _
  have hScaled : C * (d ^ ((5 : ℝ) / 3) * D) ≤
      C * (d ^ ((5 : ℝ) / 3) * velocityH3DissipationAt u t) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hPhysical hFactor) hCpos.le
  exact hTop.trans (by simpa only [d, D] using hScaled)

/-- Every strict terminal subtail of a hypothetically nonextendible
trajectory has nonintegrable five-thirds weighted full-H3 dissipation. -/
theorem thirdFullPhysical_noExtension_criticalFiveThirdsDissipation_nonintegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ¬ MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) ^ ((5 : ℝ) / 3) *
        velocityH3DissipationAt u t) (Set.Ioo b T) := by
  obtain ⟨C, hCpos, c, hc, hLower⟩ :=
    thirdFullPhysical_noExtension_harmonicCriticalFiveThirdsDissipation244
      hH3 hNoExtension hClass b hb
  intro hWeighted
  have hTail : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) ^ ((5 : ℝ) / 3) *
        velocityH3DissipationAt u t) (Set.Ioo c T) := by
    apply hWeighted.mono_set
    intro t ht
    exact ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hScaled : MeasureTheory.IntegrableOn
      (fun t : ℝ => C * ((T - t) ^ ((5 : ℝ) / 3) *
        velocityH3DissipationAt u t)) (Set.Ioo c T) :=
    hTail.const_mul C
  have hReciprocal : MeasureTheory.IntegrableOn
      (fun t : ℝ => 1 / (T - t)) (Set.Ioo c T) := by
    apply Integrable.mono' hScaled
    · exact (show Measurable (fun t : ℝ => 1 / (T - t)) by
        fun_prop).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hd : 0 < T - t := sub_pos.mpr ht.2
      have hWeightNonneg : 0 ≤ C * ((T - t) ^ ((5 : ℝ) / 3) *
          velocityH3DissipationAt u t) := by
        exact mul_nonneg hCpos.le
          (mul_nonneg (Real.rpow_nonneg hd.le _)
            (velocityH3DissipationAt_nonneg u t))
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hd)]
      simpa only [Real.norm_eq_abs, abs_of_nonneg hWeightNonneg] using
        hLower t ht
  exact not_integrableOn_one_div_terminalDistance hc.2 hReciprocal

/-- Exact critical-weight conditional continuation on any strict tail. -/
theorem thirdFullPhysical_criticalFiveThirdsDissipation_strictTail_forcesContinuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hWeighted : IntervalIntegrable
      (fun t : ℝ => (T - t) ^ ((5 : ℝ) / 3) *
        velocityH3DissipationAt u t) volume b T) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  classical
  by_contra hNoExtension
  have hForbidden :=
    thirdFullPhysical_noExtension_criticalFiveThirdsDissipation_nonintegrable244
      hH3 hNoExtension hClass b hb
  apply hForbidden
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).mp
    hWeighted

/-- Exact critical-weight conditional continuation on the original
H3 energy-class interval. -/
theorem thirdFullPhysical_criticalFiveThirdsDissipation_energyTail_forcesContinuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hWeighted : IntervalIntegrable
      (fun t : ℝ => (T - t) ^ ((5 : ℝ) / 3) *
        velocityH3DissipationAt u t) volume a T) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  let b : ℝ := h3BKMKineticTailMidpoint a T
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  have hFull : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) ^ ((5 : ℝ) / 3) *
        velocityH3DissipationAt u t) (Set.Ioo a T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      hClass.terminal_start.2.le).mp hWeighted
  have hTail : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) ^ ((5 : ℝ) / 3) *
        velocityH3DissipationAt u t) (Set.Ioo b T) := by
    apply hFull.mono_set
    intro t ht
    exact ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hTailInt : IntervalIntegrable
      (fun t : ℝ => (T - t) ^ ((5 : ℝ) / 3) *
        velocityH3DissipationAt u t) volume b T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).mpr hTail
  exact thirdFullPhysical_criticalFiveThirdsDissipation_strictTail_forcesContinuation244
    hH3 hClass b hb hTailInt

end
end PrimeTensor.FirstMonomialTriad
