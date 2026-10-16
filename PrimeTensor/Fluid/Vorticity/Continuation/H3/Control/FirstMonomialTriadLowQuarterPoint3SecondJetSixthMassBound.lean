import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetL2NormIntegralBridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzQuarticL2L6
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Genuine sixth-power mass of all 27 second Schwartz jets

The earlier quantitative 27-slot homogeneous Sobolev inequality controls
`∑ (eLpNorm jet 6)^2` by `S² * ofReal(card(Axis.three) * E3)`.

This module identifies the actual sixth-power Schwartz integral with the
sixth power of the finite L6 seminorm, then bounds the *sum* of all 27
sixth-power integrals by the cube of the 27-slot squared L6 aggregate.
No artificial factor of 27 is introduced, and no derivatives are commuted.
The final estimate is an inequality in ENNReal, with the real E3 term explicitly
converted by `ENNReal.ofReal`.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv ENNReal NNReal

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSecondJetSixthMass (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual real sixth-power integral is the sixth power of the finite
Schwartz L6 seminorm, represented in extended nonnegative reals. -/
theorem lowNormalSchwartz_eLpNorm_six_pow_eq_ofReal_integral
    (g : SchwartzMap V3 ℝ) :
    (eLpNorm (g : V3 → ℝ) (ENNReal.ofReal 6) (volume : Measure V3)) ^ 6 =
      ENNReal.ofReal (∫ ξ : V3, (g ξ) ^ 6) := by
  have hMem : MemLp (g : V3 → ℝ) (ENNReal.ofReal 6)
      (volume : Measure V3) :=
    g.memLp (ENNReal.ofReal 6) (volume : Measure V3)
  have hFormula :
      eLpNorm (g : V3 → ℝ) (ENNReal.ofReal 6) (volume : Measure V3) =
        ENNReal.ofReal
          ((∫ ξ : V3, ‖g ξ‖ ^ (6 : ℝ)) ^ ((6 : ℝ)⁻¹)) := by
    simpa only [show (ENNReal.ofReal (6 : ℝ)).toReal = (6 : ℝ) by norm_num] using
      (hMem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp))
  have hIntegralPower :
      (∫ ξ : V3, ‖g ξ‖ ^ (6 : ℝ)) =
        (∫ ξ : V3, (g ξ) ^ (6 : ℕ)) := by
    apply integral_congr_ae
    filter_upwards with ξ
    calc
      ‖g ξ‖ ^ (6 : ℝ) = ‖g ξ‖ ^ (6 : ℕ) :=
        Real.rpow_natCast (‖g ξ‖) 6
      _ = |(g ξ) ^ 6| := by
        rw [Real.norm_eq_abs, ← abs_pow]
      _ = (g ξ) ^ 6 := abs_of_nonneg (by positivity)
  have hSixthNonneg : 0 ≤ (∫ ξ : V3, (g ξ) ^ 6) :=
    integral_nonneg (fun ξ => by positivity)
  have hRoot :
      ((∫ ξ : V3, (g ξ) ^ 6) ^ ((6 : ℝ)⁻¹)) ^ (6 : ℕ) =
        (∫ ξ : V3, (g ξ) ^ 6) := by
    exact Real.rpow_inv_natCast_pow hSixthNonneg
      (by norm_num : (6 : ℕ) ≠ 0)
  rw [hIntegralPower] at hFormula
  calc
    (eLpNorm (g : V3 → ℝ) (ENNReal.ofReal 6) (volume : Measure V3)) ^ 6 =
        (ENNReal.ofReal
          ((∫ ξ : V3, (g ξ) ^ 6) ^ ((6 : ℝ)⁻¹))) ^ 6 :=
      congrArg (fun z : ℝ≥0∞ => z ^ 6) hFormula
    _ = ENNReal.ofReal
          (((∫ ξ : V3, (g ξ) ^ 6) ^ ((6 : ℝ)⁻¹)) ^ 6) :=
      (ENNReal.ofReal_pow (Real.rpow_nonneg hSixthNonneg _) 6).symm
    _ = ENNReal.ofReal (∫ ξ : V3, (g ξ) ^ 6) :=
      congrArg ENNReal.ofReal hRoot

/-- For any finite family of nonnegative extended masses, the sum of cubes
is at most the cube of the sum. This has coefficient one even at infinity. -/
private theorem lowNormal_finset_sum_cubes_le_cube
    {J : Type*} [Fintype J] (b : J → ℝ≥0∞) :
    (∑ p : J, (b p) ^ 3) ≤ (∑ p : J, b p) ^ 3 := by
  classical
  let T : ℝ≥0∞ := ∑ p : J, b p
  have hSlot (p : J) : b p ≤ T := by
    dsimp [T]
    exact Finset.single_le_sum
      (fun q _ => (bot_le : (0 : ℝ≥0∞) ≤ b q))
      (Finset.mem_univ p)
  have hEach (p : J) : (b p) ^ 3 ≤ T ^ 2 * b p := by
    have hPow : (b p) ^ 2 ≤ T ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hSlot p) 2
    calc
      (b p) ^ 3 = (b p) ^ 2 * b p := by ring
      _ ≤ T ^ 2 * b p :=
        mul_le_mul_of_nonneg_right hPow (by positivity)
  calc
    (∑ p : J, (b p) ^ 3) ≤ ∑ p : J, T ^ 2 * b p := by
      apply Finset.sum_le_sum
      intro p _
      exact hEach p
    _ = T ^ 2 * T := by
      rw [← Finset.mul_sum]
    _ = T ^ 3 := by ring

/-- Convert an arbitrary nonnegative threefold real sum to the corresponding
extended-real sum. Kept abstract to avoid reducing the Schwartz expressions. -/
private theorem lowNormal_sixth_ofReal_threefold_sum
    {J : Type*} [Fintype J] (F : J → J → J → ℝ)
    (hF : ∀ j i k, 0 ≤ F j i k) :
    (∑ j : J, ∑ i : J, ∑ k : J, ENNReal.ofReal (F j i k)) =
      ENNReal.ofReal (∑ j : J, ∑ i : J, ∑ k : J, F j i k) := by
  classical
  let C : J → J → ℝ := fun j i => ∑ k : J, F j i k
  let B : J → ℝ := fun j => ∑ i : J, C j i
  have hK (j i : J) :
      (∑ k : J, ENNReal.ofReal (F j i k)) =
        ENNReal.ofReal (C j i) := by
    exact (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (f := F j i)
      (fun k _ => hF j i k)).symm
  have hI (j : J) :
      (∑ i : J, ENNReal.ofReal (C j i)) =
        ENNReal.ofReal (B j) := by
    exact (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (f := C j)
      (fun i _ => Finset.sum_nonneg (fun k _ => hF j i k))).symm
  have hJ :
      (∑ j : J, ENNReal.ofReal (B j)) =
        ENNReal.ofReal (∑ j : J, B j) := by
    exact (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (f := B)
      (fun j _ => Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun k _ => hF j i k)))).symm
  calc
    (∑ j : J, ∑ i : J, ∑ k : J, ENNReal.ofReal (F j i k)) =
        (∑ j : J, ∑ i : J, ENNReal.ofReal (C j i)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact hK j i
    _ = (∑ j : J, ENNReal.ofReal (B j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hI j
    _ = ENNReal.ofReal (∑ j : J, B j) := hJ
    _ = _ := rfl

/-- The genuine sum of 27 sixth-power second-jet integrals is bounded by the
cube of the previously proved 27-slot squared L6 norm aggregate. -/
theorem lowNormalRealSchwartz_secondJets_sixthMass_le_L6SquareTotal_cube
    (f : A3 → SchwartzMap V3 ℝ) :
    ENNReal.ofReal
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∫ ξ : V3,
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (f j))) ξ) ^ 6) ≤
      (lowNormalRealSchwartz_secondJetsL6SquareTotal f) ^ 3 := by
  classical
  let M : A3 → A3 → A3 → ℝ := fun j i k =>
    ∫ ξ : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j))) ξ) ^ 6
  have hM (j i k : A3) : 0 ≤ M j i k :=
    integral_nonneg (fun ξ => by positivity)
  have hOfRealSum := lowNormal_sixth_ofReal_threefold_sum M hM
  have hSlot (j i k : A3) :
      ENNReal.ofReal (M j i k) =
        (lowNormalRealSchwartz_secondJetL6Square f j i k) ^ 3 := by
    unfold lowNormalRealSchwartz_secondJetL6Square
    have h := lowNormalSchwartz_eLpNorm_six_pow_eq_ofReal_integral
      (∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j)))
    calc
      ENNReal.ofReal (M j i k) =
          (eLpNorm
            (∂_{h3FourierAxisDirection i}
              (∂_{h3FourierAxisDirection k} (f j)) : SchwartzMap V3 ℝ)
            (ENNReal.ofReal 6) (volume : Measure V3)) ^ 6 := h.symm
      _ = _ := by ring
  have hCube := lowNormal_finset_sum_cubes_le_cube
    (fun p : A3 × (A3 × A3) =>
      lowNormalRealSchwartz_secondJetL6Square f p.1 p.2.1 p.2.2)
  have hCubeSlots :
      (∑ j : A3, ∑ i : A3, ∑ k : A3,
        (lowNormalRealSchwartz_secondJetL6Square f j i k) ^ 3) ≤
        (lowNormalRealSchwartz_secondJetsL6SquareTotal f) ^ 3 := by
    simpa only [Fintype.sum_prod_type, Prod.fst, Prod.snd,
      lowNormalRealSchwartz_secondJetsL6SquareTotal] using hCube
  change ENNReal.ofReal (∑ j : A3, ∑ i : A3, ∑ k : A3, M j i k) ≤ _
  calc
    ENNReal.ofReal (∑ j : A3, ∑ i : A3, ∑ k : A3, M j i k) =
        (∑ j : A3, ∑ i : A3, ∑ k : A3,
          ENNReal.ofReal (M j i k)) := hOfRealSum.symm
    _ = (∑ j : A3, ∑ i : A3, ∑ k : A3,
          (lowNormalRealSchwartz_secondJetL6Square f j i k) ^ 3) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact hSlot j i k
    _ ≤ _ := hCubeSlots

/-- The full sixth-power real Schwartz mass is controlled by the actual 81-slot
third-order energy through the quantitative homogeneous Sobolev constant.
This closes the analytic input needed by the existing quartic interpolation. -/
theorem lowNormalRealSchwartz_secondJets_sixthMass_le_sobolev_E3_cube
    (f : A3 → SchwartzMap V3 ℝ) :
    ENNReal.ofReal
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∫ ξ : V3,
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (f j))) ξ) ^ 6) ≤
      (lowNormalSecondJetSobolevConstant ^ 2 *
        ENNReal.ofReal
          ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f)) ^ 3 := by
  exact (lowNormalRealSchwartz_secondJets_sixthMass_le_L6SquareTotal_cube f).trans
    (pow_le_pow_left₀ (by positivity)
      (lowNormalRealSchwartz_secondJetsL6SquareTotal_le_sobolev_mul_E3 f) 3)

end
end PrimeTensor.FirstMonomialTriad
