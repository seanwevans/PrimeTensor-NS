import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetHomogeneousSobolev
import PrimeTensor.Bridge.Euclidean.Partials.Mixed
import Mathlib.Algebra.Order.Chebyshev

/-!
# Pointwise Fréchet/coordinate-square comparison for second Schwartz jets

The 27 second-order Schwartz jets already satisfy quantitative homogeneous
Sobolev on the actual physical `Point3` carrier. Its right side is the L² norm
of the full Fréchet derivative, whereas PrimeTensor's order-three energy is a
finite sum of squares of directional Schwartz jets.

Because `Point3` carries the finite product's sup norm, a scalar Fréchet
operator is controlled by the *sum* of absolute coordinate derivatives. The
square of that sum is at most `card (Axis Depth.three)` times the sum of the
coordinate squares. This cardinality is three. The geometric dimension factor
is genuine; identifying it with one would be an incorrect norm comparison.

This module closes the POINTWISE bridge. The integral/eLpNorm comparison with
E3 and the 27-slot quantitative Gagliardo--Nirenberg assembly are subsequent
steps. There is no Navier--Stokes regularity assertion here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSecondJetFrechetSquare (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The physical (sup-norm-carrier) Fréchet derivative satisfies the explicit
finite-coordinate Cauchy--Schwarz estimate, including all zero cases. -/
theorem lowNormalPoint3_fderiv_sq_le_card_mul_partial_sq
    (g : ScalarField3) (hC1 : SpatialC1 g) (x : Point3) :
    ‖fderiv ℝ g x‖ ^ 2 ≤
      (Fintype.card A3 : ℝ) *
        (∑ a : A3, ((spatial3.d a g) x) ^ 2) := by
  classical
  let s : ℝ := ∑ a : A3, |(spatial3.d a g) x|
  have hNorm : ‖fderiv ℝ g x‖ ≤ s := by
    dsimp [s]
    simpa [spatial3, spatial] using
      hC1.norm_fderiv_le_sum_abs_partialDeriv x
  have hSumNonneg : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg (fun a _ => abs_nonneg _)
  have hSq : ‖fderiv ℝ g x‖ ^ 2 ≤ s ^ 2 := by
    have hProduct :
        0 ≤ (s - ‖fderiv ℝ g x‖) * (s + ‖fderiv ℝ g x‖) :=
      mul_nonneg (sub_nonneg.mpr hNorm)
        (add_nonneg hSumNonneg (norm_nonneg _))
    nlinarith
  have hCS :
      s ^ 2 ≤ (Fintype.card A3 : ℝ) *
        (∑ a : A3, ((spatial3.d a g) x) ^ 2) := by
    dsimp [s]
    simpa only [Finset.card_univ, sq_abs] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset A3))
        (f := fun a : A3 => |(spatial3.d a g) x|))
  exact hSq.trans hCS

/-- The actual full Fréchet derivative of every second Schwartz jet is
pointwise controlled by the COMPLETE family of its three directional third
jets. The cardinal factor reflects the physical sup norm, not an assumption. -/
theorem lowNormalRealSchwartz_secondJet_physicalFrechet_sq_le_thirdJetSquares
    (f : A3 → SchwartzMap V3 ℝ) (j i k : A3) (x : Point3) :
    ‖fderiv ℝ
      (h3SchwartzPoint3Scalar
        (∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (f j)))) x‖ ^ 2 ≤
      (Fintype.card A3 : ℝ) *
        (∑ a : A3,
          (h3SchwartzPoint3Scalar
            (∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection i}
                (∂_{h3FourierAxisDirection k} (f j)))) x) ^ 2) := by
  let G : SchwartzMap V3 ℝ :=
    ∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k} (f j))
  have hC1 : SpatialC1 (h3SchwartzPoint3Scalar G) := by
    change ContDiff ℝ 1 (h3SchwartzPoint3Scalar G)
    rw [← lowNormalSchwartz_point3Pullback_eq G]
    exact (lowNormalSchwartz_point3Pullback G).smooth 1
  have h := lowNormalPoint3_fderiv_sq_le_card_mul_partial_sq
    (h3SchwartzPoint3Scalar G) hC1 x
  simpa only [G, h3SchwartzPoint3Scalar_spatial_d] using h

end
end PrimeTensor.FirstMonomialTriad
