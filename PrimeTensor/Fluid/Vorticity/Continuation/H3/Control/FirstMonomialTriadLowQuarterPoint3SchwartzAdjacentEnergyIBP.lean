import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3CriticalHalfLogConvexBridge
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Physical Schwartz integration by parts for the adjacent H3 energies

The critical-half balanced-shape bridge has two remaining *unproved* adjacent
Cauchy--Schwarz inequalities.  Before treating their global sums, this file
establishes the exact real Schwartz integration-by-parts identities for their
integrands.  There are no PDE trajectory or spectral compatibility assumptions.

For any real Schwartz functions F and G and physical direction v,
  integral F (D_v G) = - integral (D_v F) G.
Consequently, the actual first- and second-order H3 square energies admit
negative lower/higher-derivative pairings in the same axis ordering as the
complete physical sums.  No Fourier normalization is introduced.

This is not yet a proof of E1^2 <= E0 E2 or E2^2 <= E1 E3:
the next step must apply joint Cauchy--Schwarz to the finite axis sums.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSchwartzAdjacentEnergyIBP (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Two real Schwartz functions have an integrable physical product.
This is the explicit L2 x L2 -> L1 input for integration by parts. -/
private theorem lowNormalSchwartz_mul_integrable
    (F G : SchwartzMap V3 ℝ) :
    Integrable (fun x : V3 => F x * G x) volume := by
  change Integrable (fun x : V3 =>
    (ContinuousLinearMap.lsmul ℝ ℝ) (F x) (G x)) volume
  rw [← MeasureTheory.memLp_one_iff_integrable]
  exact (ContinuousLinearMap.lsmul ℝ ℝ).memLp_of_bilin 1
    (F.memLp 2 volume) (G.memLp 2 volume)

/-- Unconditional directional integration by parts on the genuine real
Schwartz carrier; all three product-integrability premises are discharged. -/
theorem lowNormalSchwartz_lineDeriv_integral_mul_eq_neg
    (F G : SchwartzMap V3 ℝ) (v : V3) :
    (∫ x : V3, F x * ((∂_{v} G : SchwartzMap V3 ℝ) x)) =
      -(∫ x : V3, ((∂_{v} F : SchwartzMap V3 ℝ) x) * G x) := by
  have hLeft := lowNormalSchwartz_mul_integrable (∂_{v} F) G
  have hRight := lowNormalSchwartz_mul_integrable F (∂_{v} G)
  have hFG := lowNormalSchwartz_mul_integrable F G
  have hFderiv : ∀ x : V3,
      HasLineDerivAt ℝ (F : V3 → ℝ)
        ((∂_{v} F : SchwartzMap V3 ℝ) x) x v := by
    intro x
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      (F.hasFDerivAt x).hasLineDerivAt v
  have hGderiv : ∀ x : V3,
      HasLineDerivAt ℝ (G : V3 → ℝ)
        ((∂_{v} G : SchwartzMap V3 ℝ) x) x v := by
    intro x
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      (G.hasFDerivAt x).hasLineDerivAt v
  have hIBP :=
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.lsmul ℝ ℝ)
      (show Integrable
        (fun x : V3 => (ContinuousLinearMap.lsmul ℝ ℝ)
          ((∂_{v} F : SchwartzMap V3 ℝ) x) (G x)) volume from hLeft)
      (show Integrable
        (fun x : V3 => (ContinuousLinearMap.lsmul ℝ ℝ)
          (F x) ((∂_{v} G : SchwartzMap V3 ℝ) x)) volume from hRight)
      (show Integrable
        (fun x : V3 => (ContinuousLinearMap.lsmul ℝ ℝ)
          (F x) (G x)) volume from hFG)
      (fun x _ => hFderiv x)
      (fun x _ => hGderiv x)
  change (∫ x : V3, F x * ((∂_{v} G : SchwartzMap V3 ℝ) x)) =
    -(∫ x : V3, ((∂_{v} F : SchwartzMap V3 ℝ) x) * G x) at hIBP
  exact hIBP

/-- A directional square energy equals a negative zeroth/second-derivative
pairing, with no boundary term for Schwartz data. -/
theorem lowNormalSchwartz_lineDeriv_square_by_parts
    (F : SchwartzMap V3 ℝ) (v : V3) :
    (∫ x : V3, ((∂_{v} F : SchwartzMap V3 ℝ) x) ^ 2) =
      -(∫ x : V3, F x *
        ((∂_{v} (∂_{v} F) : SchwartzMap V3 ℝ) x)) := by
  have h := lowNormalSchwartz_lineDeriv_integral_mul_eq_neg
    F (∂_{v} F) v
  have hs : (∫ x : V3, ((∂_{v} F : SchwartzMap V3 ℝ) x) ^ 2) =
      (∫ x : V3, ((∂_{v} F : SchwartzMap V3 ℝ) x) *
        ((∂_{v} F : SchwartzMap V3 ℝ) x)) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hs]
  linarith only [h]

/-- Exact physical first-order H3 energy integration-by-parts formula,
including all nine ordered velocity/axis slots. -/
theorem lowNormalRealSchwartzH3Energy1_by_parts
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy1 f =
      ∑ j : A3, ∑ i : A3,
        -(∫ x : V3, f j x *
          ((∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection i} (f j))) x)) := by
  unfold lowNormalRealSchwartzH3Energy1
  simp_rw [lowNormalSchwartz_lineDeriv_square_by_parts]

/-- Exact physical second-order H3 energy integration-by-parts formula,
including all 27 ordered velocity/axis/axis slots.  The original order
of derivatives is kept; no unproved mixed-derivative commutation is used. -/
theorem lowNormalRealSchwartzH3Energy2_by_parts
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy2 f =
      ∑ j : A3, ∑ i : A3, ∑ k : A3,
        -(∫ x : V3,
          ((∂_{h3FourierAxisDirection k} (f j)) x) *
          ((∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection i}
              (∂_{h3FourierAxisDirection k} (f j)))) x)) := by
  unfold lowNormalRealSchwartzH3Energy2
  simp_rw [lowNormalSchwartz_lineDeriv_square_by_parts]

end
end PrimeTensor.FirstMonomialTriad
