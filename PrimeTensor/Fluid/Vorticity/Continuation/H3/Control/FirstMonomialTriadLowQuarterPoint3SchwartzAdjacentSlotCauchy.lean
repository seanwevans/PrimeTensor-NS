import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzAdjacentEnergyIBP
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Actual Schwartz adjacent-energy Cauchy, slot by slot

The previous module gives the exact physical integration-by-parts identities.
We now use genuine L² Hölder/Cauchy--Schwarz for real Schwartz functions,
including both signs of their product, to obtain sharp coefficient-one
estimates for each physical ordered derivative slot.

This does not claim the full joint inequalities E1² <= E0 E2 and
E2² <= E1 E3; the finite contractions and mixed-derivative identities
needed to assemble all the slots remain a separate obligation.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv ENNReal

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeAdjacentSlotCauchy (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The signed Cauchy--Schwarz inequality for any two genuine real Schwartz
functions. No abstract inequality or additional integrability assumption is
introduced. -/
theorem lowNormalSchwartz_integral_mul_sq_le
    (F G : SchwartzMap V3 ℝ) :
    (∫ x : V3, F x * G x) ^ 2 ≤
      (∫ x : V3, (F x) ^ 2) * (∫ x : V3, (G x) ^ 2) := by
  have hf : MemLp (fun x : V3 => |F x|)
      (ENNReal.ofReal (2 : ℝ)) volume := by
    have h := (F.memLp 2 volume).norm
    simpa [Real.norm_eq_abs,
      show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] using h
  have hg : MemLp (fun x : V3 => |G x|)
      (ENNReal.ofReal (2 : ℝ)) volume := by
    have h := (G.memLp 2 volume).norm
    simpa [Real.norm_eq_abs,
      show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] using h
  have hHolder :
      (∫ x : V3, |F x| * |G x|) ≤
        (∫ x : V3, |F x| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x : V3, |G x| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall (fun x : V3 => abs_nonneg (F x)))
      (Filter.Eventually.of_forall (fun x : V3 => abs_nonneg (G x)))
      hf hg
  simp only [Real.rpow_two, sq_abs] at hHolder
  have hAbs :
      |∫ x : V3, F x * G x| ≤
        (∫ x : V3, (F x) ^ 2) ^ (1 / (2 : ℝ)) *
          (∫ x : V3, (G x) ^ 2) ^ (1 / (2 : ℝ)) := by
    calc
      _ ≤ ∫ x : V3, |F x * G x| := abs_integral_le_integral_abs
      _ = ∫ x : V3, |F x| * |G x| := by simp only [abs_mul]
      _ ≤ _ := hHolder
  have hF0 : 0 ≤ (∫ x : V3, (F x) ^ 2) :=
    integral_nonneg (fun x => sq_nonneg (F x))
  have hG0 : 0 ≤ (∫ x : V3, (G x) ^ 2) :=
    integral_nonneg (fun x => sq_nonneg (G x))
  calc
    (∫ x : V3, F x * G x) ^ 2 =
        |∫ x : V3, F x * G x| ^ 2 := (sq_abs _).symm
    _ ≤ ((∫ x : V3, (F x) ^ 2) ^ (1 / (2 : ℝ)) *
          (∫ x : V3, (G x) ^ 2) ^ (1 / (2 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hAbs 2
    _ = (∫ x : V3, (F x) ^ 2) * (∫ x : V3, (G x) ^ 2) := by
      rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
        Real.sq_sqrt hF0, Real.sq_sqrt hG0]

/-- The first-order physical derivative square on a single ordered
component/direction slot is bounded by its zeroth- and repeated-second-order
Schwartz masses with coefficient exactly one. -/
theorem lowNormalRealSchwartzH3Energy1_slot_cauchy
    (f : A3 → SchwartzMap V3 ℝ) (j i : A3) :
    (∫ x : V3, ((∂_{h3FourierAxisDirection i} (f j)) x) ^ 2) ^ 2 ≤
      (∫ x : V3, (f j x) ^ 2) *
        (∫ x : V3,
          ((∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection i} (f j))) x) ^ 2) := by
  let v : V3 := h3FourierAxisDirection i
  have hIBP := lowNormalSchwartz_lineDeriv_square_by_parts (f j) v
  have hCS := lowNormalSchwartz_integral_mul_sq_le
    (f j) (∂_{v} (∂_{v} (f j)))
  calc
    (∫ x : V3, ((∂_{v} (f j)) x) ^ 2) ^ 2 =
        (∫ x : V3, f j x * ((∂_{v} (∂_{v} (f j))) x)) ^ 2 := by
      rw [hIBP]
      ring
    _ ≤ _ := hCS

/-- The actual second-order physical derivative square on a single ordered
component/direction/direction slot is bounded by its adjacent first- and
third-order Schwartz masses, retaining the given derivative ordering. -/
theorem lowNormalRealSchwartzH3Energy2_slot_cauchy
    (f : A3 → SchwartzMap V3 ℝ) (j i k : A3) :
    (∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j))) x) ^ 2) ^ 2 ≤
      (∫ x : V3, ((∂_{h3FourierAxisDirection k} (f j)) x) ^ 2) *
        (∫ x : V3,
          ((∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection i}
              (∂_{h3FourierAxisDirection k} (f j)))) x) ^ 2) := by
  let v : V3 := h3FourierAxisDirection i
  let F : SchwartzMap V3 ℝ := ∂_{h3FourierAxisDirection k} (f j)
  have hIBP := lowNormalSchwartz_lineDeriv_square_by_parts F v
  have hCS := lowNormalSchwartz_integral_mul_sq_le F (∂_{v} (∂_{v} F))
  change (∫ x : V3, ((∂_{v} F) x) ^ 2) ^ 2 ≤
    (∫ x : V3, (F x) ^ 2) *
      (∫ x : V3, ((∂_{v} (∂_{v} F)) x) ^ 2)
  calc
    (∫ x : V3, ((∂_{v} F) x) ^ 2) ^ 2 =
        (∫ x : V3, F x * ((∂_{v} (∂_{v} F)) x)) ^ 2 := by
      rw [hIBP]
      ring
    _ ≤ _ := hCS

end
end PrimeTensor.FirstMonomialTriad
