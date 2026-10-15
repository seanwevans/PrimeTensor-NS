import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSharpAdjacentPairing
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzAdjacentSlotCauchy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Coefficient-one Cauchy and cubic interpolation for physical Schwartz H3 energies

The signed first- and second-order Laplacian pairings and the exact 27- and 81-slot
Hessian--Laplacian contractions give the full adjacent inequalities

  E1^2 <= E0 E2,       E2^2 <= E1 E3.

The previous axis-cardinality loss disappears: joint Cauchy is applied to
actual componentwise Schwartz functions, not to diagonal derivative slots.
Consequently the cubic interpolation constant is exactly one, and the
four-block energy at a positive balancing scale is at most 4 E0.
This does not claim a universal nonlinear critical-half coefficient exists.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSharpAdjacentCauchy (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-! Cauchy is first proved for a finite family of real Schwartz pairs,
independently of any fluid-specific energy expressions. -/

private theorem lowNormalSchwartz_jointIntegralCauchy
    {J : Type*} [Fintype J]
    (F G : J → SchwartzMap V3 ℝ) :
    (∑ j : J, ∫ x : V3, F j x * G j x) ^ 2 ≤
      (∑ j : J, ∫ x : V3, (F j x) ^ 2) *
        (∑ j : J, ∫ x : V3, (G j x) ^ 2) := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset J)
    (r := fun j => ∫ x : V3, F j x * G j x)
    (f := fun j => ∫ x : V3, (F j x) ^ 2)
    (g := fun j => ∫ x : V3, (G j x) ^ 2)
    (by intro j _; exact integral_nonneg (fun x => sq_nonneg (F j x)))
    (by intro j _; exact integral_nonneg (fun x => sq_nonneg (G j x)))
    (by intro j _; exact lowNormalSchwartz_integral_mul_sq_le (F j) (G j))

private theorem lowNormalSchwartz_jointIntegralCauchy_two
    {J K : Type*} [Fintype J] [Fintype K]
    (F G : J → K → SchwartzMap V3 ℝ) :
    (∑ j : J, ∑ k : K, ∫ x : V3, F j k x * G j k x) ^ 2 ≤
      (∑ j : J, ∑ k : K, ∫ x : V3, (F j k x) ^ 2) *
        (∑ j : J, ∑ k : K, ∫ x : V3, (G j k x) ^ 2) := by
  have h := lowNormalSchwartz_jointIntegralCauchy
    (J := J × K)
    (fun p : J × K => F p.1 p.2)
    (fun p : J × K => G p.1 p.2)
  simpa only [Fintype.sum_prod_type] using h

/-- The complete 27-slot Hessian mass equals the Laplacian-map norm sum. -/
private theorem lowNormalSchwartz_laplacianMap_energy2
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ j : A3, ∫ x : V3,
      (lowNormalSchwartz_axisLaplacianMap (f j) x) ^ 2) =
      lowNormalRealSchwartzH3Energy2 f := by
  calc
    _ = ∑ j : A3, ∫ x : V3,
      (lowNormalSchwartz_axisLaplacian (f j) x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        apply integral_congr_ae
        filter_upwards with x
        rw [lowNormalSchwartz_axisLaplacianMap_apply]
    _ = _ := (lowNormalRealSchwartzH3Energy2_eq_sum_axisLaplacian_sq f).symm

/-- The complete 81-slot third mass equals the first-jet Laplacian-map
norm sum, with the original ordered axes retained. -/
private theorem lowNormalSchwartz_laplacianMap_energy3
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ j : A3, ∑ k : A3, ∫ x : V3,
      (lowNormalSchwartz_axisLaplacianMap
        (∂_{h3FourierAxisDirection k} (f j)) x) ^ 2) =
      lowNormalRealSchwartzH3Energy3 f := by
  calc
    _ = ∑ j : A3, ∑ k : A3, ∫ x : V3,
      (lowNormalSchwartz_axisLaplacian
        (∂_{h3FourierAxisDirection k} (f j)) x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply integral_congr_ae
        filter_upwards with x
        rw [lowNormalSchwartz_axisLaplacianMap_apply]
    _ = _ := (lowNormalRealSchwartzH3Energy3_eq_sum_firstJet_axisLaplacian_sq f).symm

/-- Sharp coefficient-one adjacent Cauchy: **no axis-cardinality loss**
for the genuine first, zeroth, and second physical H3 energies. -/
theorem lowNormalRealSchwartzH3Energy1_sq_le_E0_mul_E2
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy1 f) ^ 2 ≤
      lowNormalRealSchwartzH3Energy0 f *
        lowNormalRealSchwartzH3Energy2 f := by
  have hPair := lowNormalRealSchwartzH3Energy1_eq_neg_sum_laplacian_pair f
  have hCS := lowNormalSchwartz_jointIntegralCauchy
    (fun j : A3 => f j)
    (fun j : A3 => lowNormalSchwartz_axisLaplacianMap (f j))
  have hUpper := lowNormalSchwartz_laplacianMap_energy2 f
  have hLower :
      (∑ j : A3, ∫ x : V3, (f j x) ^ 2) =
        lowNormalRealSchwartzH3Energy0 f := rfl
  calc
    _ = (∑ j : A3, ∫ x : V3,
          f j x * lowNormalSchwartz_axisLaplacianMap (f j) x) ^ 2 := by
        rw [hPair]
        ring
    _ ≤ (∑ j : A3, ∫ x : V3, (f j x) ^ 2) *
        (∑ j : A3, ∫ x : V3,
          (lowNormalSchwartz_axisLaplacianMap (f j) x) ^ 2) := hCS
    _ = lowNormalRealSchwartzH3Energy0 f *
        lowNormalRealSchwartzH3Energy2 f := by
        rw [hLower, hUpper]

/-- Sharp coefficient-one adjacent Cauchy for the complete second,
first and third physical H3 energy blocks. -/
theorem lowNormalRealSchwartzH3Energy2_sq_le_E1_mul_E3
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy2 f) ^ 2 ≤
      lowNormalRealSchwartzH3Energy1 f *
        lowNormalRealSchwartzH3Energy3 f := by
  have hPair := lowNormalRealSchwartzH3Energy2_eq_neg_firstJet_laplacian_pair f
  have hCS := lowNormalSchwartz_jointIntegralCauchy_two
    (fun j k : A3 => ∂_{h3FourierAxisDirection k} (f j))
    (fun j k : A3 => lowNormalSchwartz_axisLaplacianMap
      (∂_{h3FourierAxisDirection k} (f j)))
  have hUpper := lowNormalSchwartz_laplacianMap_energy3 f
  have hLower :
      (∑ j : A3, ∑ k : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection k} (f j) : SchwartzMap V3 ℝ) x) ^ 2) =
        lowNormalRealSchwartzH3Energy1 f := rfl
  calc
    _ = (∑ j : A3, ∑ k : A3, ∫ x : V3,
          ((∂_{h3FourierAxisDirection k} (f j) : SchwartzMap V3 ℝ) x) *
            lowNormalSchwartz_axisLaplacianMap
              (∂_{h3FourierAxisDirection k} (f j)) x) ^ 2 := by
        rw [hPair]
        ring
    _ ≤ (∑ j : A3, ∑ k : A3, ∫ x : V3,
          ((∂_{h3FourierAxisDirection k} (f j) : SchwartzMap V3 ℝ) x) ^ 2) *
        (∑ j : A3, ∑ k : A3, ∫ x : V3,
          (lowNormalSchwartz_axisLaplacianMap
            (∂_{h3FourierAxisDirection k} (f j)) x) ^ 2) := hCS
    _ = lowNormalRealSchwartzH3Energy1 f *
        lowNormalRealSchwartzH3Energy3 f := by
        rw [hLower, hUpper]

/-- Unconditional exact-constant cubic interpolation for genuine real
Schwartz H3 energy blocks, with no independent interpolation assumptions. -/
theorem lowNormalRealSchwartzH3Energy_sharp_cubicLogConvex
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy1 f) ^ 3 ≤
        (lowNormalRealSchwartzH3Energy0 f) ^ 2 *
          lowNormalRealSchwartzH3Energy3 f
      ∧
    (lowNormalRealSchwartzH3Energy2 f) ^ 3 ≤
        lowNormalRealSchwartzH3Energy0 f *
          (lowNormalRealSchwartzH3Energy3 f) ^ 2 := by
  exact criticalHalf_adjacentCauchy_implies_cubicLogConvex
    (lowNormalRealSchwartzH3Energy0 f)
    (lowNormalRealSchwartzH3Energy1 f)
    (lowNormalRealSchwartzH3Energy2 f)
    (lowNormalRealSchwartzH3Energy3 f)
    (lowNormalRealSchwartzH3Energy0_nonneg f)
    (lowNormalRealSchwartzH3Energy1_nonneg f)
    (lowNormalRealSchwartzH3Energy2_nonneg f)
    (lowNormalRealSchwartzH3Energy3_nonneg f)
    (lowNormalRealSchwartzH3Energy1_sq_le_E0_mul_E2 f)
    (lowNormalRealSchwartzH3Energy2_sq_le_E1_mul_E3 f)

/-- At the positive balance scale, the original exact four-block bound
of `4 E0` is now unconditional for actual physical Schwartz profiles. -/
theorem lowNormalRealSchwartzH3Energy_sharp_balancedScale_upper
    (f : A3 → SchwartzMap V3 ℝ)
    (scale : ℝ) (hscale : 0 < scale)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hBalance : scale ^ 6 * lowNormalRealSchwartzH3Energy3 f =
      lowNormalRealSchwartzH3Energy0 f) :
    lowNormalRealSchwartzH3Energy0 f +
        scale ^ 2 * lowNormalRealSchwartzH3Energy1 f +
        scale ^ 4 * lowNormalRealSchwartzH3Energy2 f +
        scale ^ 6 * lowNormalRealSchwartzH3Energy3 f ≤
      4 * lowNormalRealSchwartzH3Energy0 f := by
  obtain ⟨hOne, hTwo⟩ :=
    lowNormalRealSchwartzH3Energy_sharp_cubicLogConvex f
  exact criticalHalf_balancedScale_energyPolynomial_upper
    (lowNormalRealSchwartzH3Energy0 f)
    (lowNormalRealSchwartzH3Energy1 f)
    (lowNormalRealSchwartzH3Energy2 f)
    (lowNormalRealSchwartzH3Energy3 f)
    scale hE0
    (lowNormalRealSchwartzH3Energy1_nonneg f)
    (lowNormalRealSchwartzH3Energy2_nonneg f)
    hscale hOne hTwo hBalance

end
end PrimeTensor.FirstMonomialTriad
