import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3IntegerCriticalHalfBridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzAdjacentSlotCauchy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Exact Schwartz quartic interpolation from the existing L² Cauchy theorem

For a real Schwartz function g on the physical Euclidean three-carrier,

  (∫ g⁴)² ≤ (∫ g²) (∫ g⁶).

This is the precise coefficient-one L²/L⁶ interpolation step in the
integer-order Gagliardo--Nirenberg route. It is an actual inequality,
not an assumed quantitative Sobolev hypothesis. Rather than introducing a
new Lp API, form g³ as a genuine Schwartz function with the existing
continuous bilinear Schwartz pairing, then use the project's proved signed
L² Cauchy--Schwarz inequality for g and g³.

The result is extended to arbitrary finite families and to the actual
27 second-order Schwartz derivative slots. The quantitative homogeneous
H¹ → L⁶ constant is NOT supplied by this module, so the final critical-half
coefficient is still not formalized.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSchwartzQuarticL2L6 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- A Schwartz cube, obtained entirely inside Schwartz space. -/
noncomputable def lowNormalSchwartz_cube
    (g : SchwartzMap V3 ℝ) : SchwartzMap V3 ℝ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) g
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) g g)

/-- The actual pointwise value of the Schwartz cube. -/
theorem lowNormalSchwartz_cube_apply
    (g : SchwartzMap V3 ℝ) (x : V3) :
    lowNormalSchwartz_cube g x = (g x) ^ 3 := by
  unfold lowNormalSchwartz_cube
  simp only [SchwartzMap.pairing_apply]
  change g x * (g x * g x) = (g x) ^ 3
  ring

/-- Coefficient-one L⁴ interpolation, with no auxiliary Cauchy hypothesis.
Both the third power and its square are represented by Schwartz integrals,
so their finite integrability is intrinsic. -/
theorem lowNormalSchwartz_integral_fourth_sq_le_second_mul_sixth
    (g : SchwartzMap V3 ℝ) :
    (∫ x : V3, (g x) ^ 4) ^ 2 ≤
      (∫ x : V3, (g x) ^ 2) *
        (∫ x : V3, (g x) ^ 6) := by
  let c : SchwartzMap V3 ℝ := lowNormalSchwartz_cube g
  have hc (x : V3) : c x = (g x) ^ 3 :=
    lowNormalSchwartz_cube_apply g x
  have hFourth :
      (∫ x : V3, g x * c x) = ∫ x : V3, (g x) ^ 4 := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hc x]
    ring
  have hSixth :
      (∫ x : V3, (c x) ^ 2) = ∫ x : V3, (g x) ^ 6 := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hc x]
    ring
  have hCS := lowNormalSchwartz_integral_mul_sq_le g c
  rw [hFourth, hSixth] at hCS
  exact hCS

/-- Joint coefficient-one quartic interpolation for any finite family of
Schwartz functions, with no cardinality factor. -/
theorem lowNormalSchwartz_family_integral_fourth_sq_le_second_mul_sixth
    {J : Type*} [Fintype J]
    (F : J → SchwartzMap V3 ℝ) :
    (∑ j : J, ∫ x : V3, (F j x) ^ 4) ^ 2 ≤
      (∑ j : J, ∫ x : V3, (F j x) ^ 2) *
        (∑ j : J, ∫ x : V3, (F j x) ^ 6) := by
  classical
  let C : J → SchwartzMap V3 ℝ := fun j => lowNormalSchwartz_cube (F j)
  have hc (j : J) (x : V3) : C j x = (F j x) ^ 3 :=
    lowNormalSchwartz_cube_apply (F j) x
  have hFourth :
      (∑ j : J, ∫ x : V3, F j x * C j x) =
      ∑ j : J, ∫ x : V3, (F j x) ^ 4 := by
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards with x
    rw [hc j x]
    ring
  have hSixth :
      (∑ j : J, ∫ x : V3, (C j x) ^ 2) =
      ∑ j : J, ∫ x : V3, (F j x) ^ 6 := by
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards with x
    rw [hc j x]
    ring
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset J)
    (r := fun j => ∫ x : V3, F j x * C j x)
    (f := fun j => ∫ x : V3, (F j x) ^ 2)
    (g := fun j => ∫ x : V3, (C j x) ^ 2)
    (by intro j _; exact integral_nonneg (fun x => sq_nonneg (F j x)))
    (by intro j _; exact integral_nonneg (fun x => sq_nonneg (C j x)))
    (by intro j _; exact lowNormalSchwartz_integral_mul_sq_le (F j) (C j))
  rw [hFourth, hSixth] at hCS
  exact hCS

/-- The full 27-slot second-derivative L⁴ integral is interpolated against
its exact physical order-two energy, coefficient one, and the genuine
sixth-power derivative integral. No PDE or solenoidality is assumed. -/
theorem lowNormalRealSchwartz_secondJets_quartic_sq_le_E2_mul_sixth
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∫ x : V3,
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (f j))) x) ^ 4) ^ 2 ≤
      lowNormalRealSchwartzH3Energy2 f *
        (∑ j : A3, ∑ i : A3, ∑ k : A3,
          ∫ x : V3,
            ((∂_{h3FourierAxisDirection i}
              (∂_{h3FourierAxisDirection k} (f j))) x) ^ 6) := by
  classical
  let F : A3 × (A3 × A3) → SchwartzMap V3 ℝ :=
    fun p => ∂_{h3FourierAxisDirection p.2.1}
      (∂_{h3FourierAxisDirection p.2.2} (f p.1))
  have h := lowNormalSchwartz_family_integral_fourth_sq_le_second_mul_sixth F
  change
    (∑ p : A3 × (A3 × A3), ∫ x : V3, (F p x) ^ 4) ^ 2 ≤
      (∑ p : A3 × (A3 × A3), ∫ x : V3, (F p x) ^ 2) *
        (∑ p : A3 × (A3 × A3), ∫ x : V3, (F p x) ^ 6) at h
  simpa only [Fintype.sum_prod_type, F, lowNormalRealSchwartzH3Energy2] using h

end
end PrimeTensor.FirstMonomialTriad
