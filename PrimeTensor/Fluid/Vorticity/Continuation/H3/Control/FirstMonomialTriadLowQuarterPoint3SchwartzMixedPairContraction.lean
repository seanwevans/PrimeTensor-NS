import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzUnconditionalLogConvex
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzAdjacentEnergyIBP
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The physical Schwartz mixed-derivative pair contraction

The previous unconditional cubic bounds incur an axis-cardinality factor.
The key missing identity comes from the symmetry of two classical directional
Schwartz derivatives, combined with two genuine whole-space integrations by
parts. We prove the exact pairwise identity, with no Fourier convention and
no equation-of-motion assumptions:

  integral (D_u D_u F) * (D_v D_v F)
    = integral (D_u D_v F)^2.

The aggregate Hessian/Laplacian contraction is a subsequent finite-sum step;
this module asserts only the actual pairwise identity. The derivatives and
integrals are the same real Schwartz operators used by the H3 energy blocks.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3
private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeMixedPair (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real Schwartz functions have commuting directional derivatives; this
comes from symmetry of their genuine second Fréchet derivative. -/
theorem lowNormalSchwartz_lineDeriv_comm
    (F : SchwartzMap V3 ℝ) (u v : V3) :
    (∂_{u} (∂_{v} F) : SchwartzMap V3 ℝ) =
      (∂_{v} (∂_{u} F) : SchwartzMap V3 ℝ) := by
  have hv : (⇑(∂_{v} F : SchwartzMap V3 ℝ) : V3 → ℝ) =
      fun y : V3 => (fderiv ℝ (F : V3 → ℝ) y) v := by
    funext y
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv v F y
  have hu : (⇑(∂_{u} F : SchwartzMap V3 ℝ) : V3 → ℝ) =
      fun y : V3 => (fderiv ℝ (F : V3 → ℝ) y) u := by
    funext y
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv u F y
  ext x
  have hfC2 : ContDiff ℝ 2 (F : V3 → ℝ) := F.smooth 2
  have hDiff : DifferentiableAt ℝ (fderiv ℝ (F : V3 → ℝ)) x :=
    (hfC2.fderiv_right (by norm_num)).differentiable_one.differentiableAt
  have hSymm : IsSymmSndFDerivAt ℝ (F : V3 → ℝ) x :=
    hfC2.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hLeft :
      (fderiv ℝ (fun y : V3 => (fderiv ℝ (F : V3 → ℝ) y) v) x) u =
      ((fderiv ℝ (fderiv ℝ (F : V3 → ℝ)) x) u) v := by
    rw [fderiv_clm_apply hDiff (differentiableAt_const (c := v))]
    simp
  have hRight :
      (fderiv ℝ (fun y : V3 => (fderiv ℝ (F : V3 → ℝ) y) u) x) v =
      ((fderiv ℝ (fderiv ℝ (F : V3 → ℝ)) x) v) u := by
    rw [fderiv_clm_apply hDiff (differentiableAt_const (c := u))]
    simp
  calc
    (∂_{u} (∂_{v} F) : SchwartzMap V3 ℝ) x =
        (fderiv ℝ (fun y : V3 => (fderiv ℝ (F : V3 → ℝ) y) v) x) u := by
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact congrArg (fun g : V3 → ℝ => (fderiv ℝ g x) u) hv
    _ = ((fderiv ℝ (fderiv ℝ (F : V3 → ℝ)) x) u) v := hLeft
    _ = ((fderiv ℝ (fderiv ℝ (F : V3 → ℝ)) x) v) u := hSymm.eq u v
    _ = (fderiv ℝ (fun y : V3 => (fderiv ℝ (F : V3 → ℝ) y) u) x) v := hRight.symm
    _ = (∂_{v} (∂_{u} F) : SchwartzMap V3 ℝ) x := by
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact (congrArg (fun g : V3 → ℝ => (fderiv ℝ g x) v) hu).symm

/-- Exact pairwise Laplacian/Hessian contraction for a real Schwartz scalar.
No Fourier transform, boundary term, or mixed-derivative hypothesis remains. -/
theorem lowNormalSchwartz_secondLineDeriv_pair_eq_mixed_square
    (F : SchwartzMap V3 ℝ) (u v : V3) :
    (∫ x : V3,
        ((∂_{u} (∂_{u} F) : SchwartzMap V3 ℝ) x) *
          ((∂_{v} (∂_{v} F) : SchwartzMap V3 ℝ) x)) =
      ∫ x : V3,
        ((∂_{u} (∂_{v} F) : SchwartzMap V3 ℝ) x) ^ 2 := by
  have hSwapInside := lowNormalSchwartz_lineDeriv_comm (∂_{v} F) u v
  have hSwapOutside := lowNormalSchwartz_lineDeriv_comm F v u
  have hIBP1 := lowNormalSchwartz_lineDeriv_integral_mul_eq_neg
    (∂_{u} F) (∂_{v} (∂_{v} F)) u
  have hIBP2 := lowNormalSchwartz_lineDeriv_integral_mul_eq_neg
    (∂_{u} F) (∂_{u} (∂_{v} F)) v
  -- Each integration-by-parts theorem is already an equality of real
  -- integrals.  Rewrite at the Schwartz-function level *before* comparing
  -- them, rather than elaborating fresh untyped products in a `calc` chain.
  rw [hSwapInside] at hIBP1
  rw [hSwapOutside] at hIBP2
  have hNeg := hIBP1.symm.trans hIBP2
  have hProduct := neg_inj.mp hNeg
  calc
    (∫ x : V3,
      ((∂_{u} (∂_{u} F) : SchwartzMap V3 ℝ) x) *
      ((∂_{v} (∂_{v} F) : SchwartzMap V3 ℝ) x)) =
      (∫ x : V3,
        ((∂_{u} (∂_{v} F) : SchwartzMap V3 ℝ) x) *
        ((∂_{u} (∂_{v} F) : SchwartzMap V3 ℝ) x)) := hProduct
    _ = ∫ x : V3,
      ((∂_{u} (∂_{v} F) : SchwartzMap V3 ℝ) x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        ring

/-- The concrete physical ordered coordinate directions satisfy the exact
pairwise contraction, independently for each velocity component. -/
theorem lowNormalRealSchwartz_axis_secondPair_eq_mixedSquare
    (f : A3 → SchwartzMap V3 ℝ) (j i k : A3) :
    (∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection i} (f j))) x) *
      ((∂_{h3FourierAxisDirection k}
        (∂_{h3FourierAxisDirection k} (f j))) x)) =
    ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j))) x) ^ 2 := by
  exact lowNormalSchwartz_secondLineDeriv_pair_eq_mixed_square
    (f j) (h3FourierAxisDirection i) (h3FourierAxisDirection k)

end
end PrimeTensor.FirstMonomialTriad
