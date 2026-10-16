import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3QuantitativeCutoffSobolev
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Split quantitative cutoff Sobolev estimate on Point3

The previous theorem controls a cutoff by the L² norm of
  ‖Dg‖ + (C / R) |g|.
Here the triangle inequality and the exact scalar-multiplication rule
separate these two contributions with coefficient one:

  ‖χ_R g‖₆ ≤ S (‖Dg‖₂ + (C / R) ‖g‖₂).

The coefficient S is the existing three-dimensional compact-support
Sobolev constant and C is the fixed cutoff constant. Both are independent
of the radius and the function. This is a quantitative, unconditional
analytic inequality, not merely an L⁶ membership statement.

The homogeneous whole-space inequality follows mathematically after
R → ∞, but the limit passage is NOT asserted in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3CriticalSplitSobolev
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Minkowski and scalar multiplication split the radius-dependent
cutoff majorant into its genuine first-derivative and zeroth-order L² norms.
The constant in front of each term is exactly one. -/
theorem radius_cutoff_majorant_eLpNorm_le_split
    (g : ScalarField3)
    (hC1 : SpatialC1 g)
    (hg2 : MemLp g (ENNReal.ofReal 2) volume)
    (hDg2 : MemLp (fun x : Point3 => fderiv ℝ g x)
      (ENNReal.ofReal 2) volume)
    (C : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    eLpNorm (fun x : Point3 =>
        ‖fderiv ℝ g x‖ + ((C : ℝ) / R) * |g x|)
      (ENNReal.ofReal 2) volume ≤
      eLpNorm (fun x : Point3 => fderiv ℝ g x)
        (ENNReal.ofReal 2) volume +
        ‖((C : ℝ) / R)‖ₑ *
          eLpNorm g (ENNReal.ofReal 2) volume := by
  have hDerivativeMeas :
      AEStronglyMeasurable
        (fun x : Point3 => ‖fderiv ℝ g x‖) volume :=
    hDg2.norm.aestronglyMeasurable
  have hScaledMeas :
      AEStronglyMeasurable
        (fun x : Point3 => ((C : ℝ) / R) * |g x|) volume := by
    simpa only [Real.norm_eq_abs] using
      ((hg2.norm).const_mul ((C : ℝ) / R)).aestronglyMeasurable
  have hTriangle :
      eLpNorm (fun x : Point3 =>
          ‖fderiv ℝ g x‖ + ((C : ℝ) / R) * |g x|)
        (ENNReal.ofReal 2) volume ≤
        eLpNorm (fun x : Point3 => ‖fderiv ℝ g x‖)
          (ENNReal.ofReal 2) volume +
        eLpNorm (fun x : Point3 => ((C : ℝ) / R) * |g x|)
          (ENNReal.ofReal 2) volume := by
    have hFunction :
        (fun x : Point3 =>
          ‖fderiv ℝ g x‖ + ((C : ℝ) / R) * |g x|) =
          (fun x : Point3 => ‖fderiv ℝ g x‖) +
            (fun x : Point3 => ((C : ℝ) / R) * |g x|) := by
      funext x
      rfl
    rw [hFunction]
    exact eLpNorm_add_le
      (μ := (volume : Measure Point3))
      (p := ENNReal.ofReal 2)
      (f := fun x : Point3 => ‖fderiv ℝ g x‖)
      (g := fun x : Point3 => ((C : ℝ) / R) * |g x|)
      hDerivativeMeas hScaledMeas
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)
  have hDerivativeNorm :
      eLpNorm (fun x : Point3 => ‖fderiv ℝ g x‖)
        (ENNReal.ofReal 2) volume =
      eLpNorm (fun x : Point3 => fderiv ℝ g x)
        (ENNReal.ofReal 2) volume := by
    exact eLpNorm_norm (fun x : Point3 => fderiv ℝ g x)
  have hScalarNorm :
      eLpNorm (fun x : Point3 => ((C : ℝ) / R) * |g x|)
        (ENNReal.ofReal 2) volume =
      ‖((C : ℝ) / R)‖ₑ *
        eLpNorm (fun x : Point3 => |g x|)
          (ENNReal.ofReal 2) volume := by
    have hPointwise :
        ((C : ℝ) / R) • (fun x : Point3 => |g x|) =
          (fun x : Point3 => ((C : ℝ) / R) * |g x|) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hPointwise]
    exact eLpNorm_const_smul ((C : ℝ) / R)
      (fun x : Point3 => |g x|)
      (ENNReal.ofReal 2) (volume : Measure Point3)
  have hZerothNorm :
      eLpNorm (fun x : Point3 => |g x|)
        (ENNReal.ofReal 2) volume =
      eLpNorm g (ENNReal.ofReal 2) volume := by
    simpa only [Real.norm_eq_abs] using
      (eLpNorm_norm g (p := ENNReal.ofReal 2) (μ := volume))
  calc
    eLpNorm (fun x : Point3 =>
        ‖fderiv ℝ g x‖ + ((C : ℝ) / R) * |g x|)
        (ENNReal.ofReal 2) volume ≤
      eLpNorm (fun x : Point3 => ‖fderiv ℝ g x‖)
        (ENNReal.ofReal 2) volume +
      eLpNorm (fun x : Point3 => ((C : ℝ) / R) * |g x|)
        (ENNReal.ofReal 2) volume := hTriangle
    _ = eLpNorm (fun x : Point3 => fderiv ℝ g x)
          (ENNReal.ofReal 2) volume +
        ‖((C : ℝ) / R)‖ₑ *
          eLpNorm g (ENNReal.ofReal 2) volume := by
      rw [hDerivativeNorm, hScalarNorm, hZerothNorm]

/-- Quantitative radius-dependent Sobolev with numerical L² norms on the
right. The cutoff constant C is uniform in g and R, while the Sobolev
constant S is precisely the existing 3D Mathlib constant. -/
theorem exists_uniform_radius_cutoff_quantitative_split_L6
    {g : ScalarField3}
    (hC1 : SpatialC1 g)
    (hg2 : MemLp g (ENNReal.ofReal 2) volume)
    (hDg2 : MemLp (fun x : Point3 => fderiv ℝ g x)
      (ENNReal.ofReal 2) volume) :
    ∃ C : ℝ≥0, ∀ {R : ℝ} (hR : 0 < R),
      eLpNorm (h3LandauCutoffField R hR g)
          (ENNReal.ofReal 6) volume ≤
        ((MeasureTheory.SNormLESNormFDerivOfEqConst
          ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
          (eLpNorm (fun x : Point3 => fderiv ℝ g x)
              (ENNReal.ofReal 2) volume +
            ‖((C : ℝ) / R)‖ₑ *
              eLpNorm g (ENNReal.ofReal 2) volume) := by
  obtain ⟨C, hCutoff⟩ :=
    exists_uniform_radius_cutoff_quantitative_L6 hC1 hg2 hDg2
  refine ⟨C, ?_⟩
  intro R hR
  calc
    eLpNorm (h3LandauCutoffField R hR g)
        (ENNReal.ofReal 6) volume ≤
      ((MeasureTheory.SNormLESNormFDerivOfEqConst
        ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fun x : Point3 =>
          ‖fderiv ℝ g x‖ + ((C : ℝ) / R) * |g x|)
          (ENNReal.ofReal 2) volume := hCutoff hR
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left
        (radius_cutoff_majorant_eLpNorm_le_split
          g hC1 hg2 hDg2 C hR)
        (by positivity)

end
end Euclidean
end Bridge
end PrimeTensor
