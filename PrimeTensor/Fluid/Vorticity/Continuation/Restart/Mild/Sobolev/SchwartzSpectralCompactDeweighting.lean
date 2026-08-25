import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralCompactDensity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SpectralL1
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Deweighting smooth compact spectral approximants

The weighted spectral density rung gives smooth compactly-supported representatives
`g` in the solver state.  This file proves that multiplying such a representative
by the exact reciprocal H³ frequency weight produces another smooth compactly-supported
function, hence a Schwartz function.

This is the bridge needed to feed weighted spectral approximants into the already-proved
Schwartz product/convolution identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal ContDiff

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralCompactDeweighting
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Smoothness of the exact reciprocal weight -/

/-- The Fourier square-gradient factor is smooth. -/
theorem contDiff_h3FourierGradientSquare :
    ContDiff ℝ ∞ h3FourierGradientSquare := by
  unfold h3FourierGradientSquare
  have hNormSq :
      ContDiff ℝ ∞ (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 2) :=
    contDiff_id.norm_sq ℝ
  exact contDiff_const.mul hNormSq

/-- The exact polynomial H³ weight-square is smooth. -/
theorem contDiff_h3SobolevFrequencyWeightSq :
    ContDiff ℝ ∞ h3SobolevFrequencyWeightSq := by
  unfold h3SobolevFrequencyWeightSq
  have hq : ContDiff ℝ ∞ h3FourierGradientSquare :=
    contDiff_h3FourierGradientSquare
  exact ((contDiff_const.add hq).add (hq.pow 2)).add (hq.pow 3)

/-- The exact H³ frequency weight is smooth because its square is everywhere positive. -/
theorem contDiff_h3SobolevFrequencyWeight :
    ContDiff ℝ ∞ h3SobolevFrequencyWeight := by
  unfold h3SobolevFrequencyWeight
  apply contDiff_h3SobolevFrequencyWeightSq.sqrt
  intro ξ
  exact ne_of_gt <|
    lt_of_lt_of_le zero_lt_one
      (one_le_h3SobolevFrequencyWeightSq ξ)

/-- The exact reciprocal H³ frequency weight is smooth. -/
theorem contDiff_h3SobolevFrequencyWeightInv :
    ContDiff ℝ ∞ h3SobolevFrequencyWeightInv := by
  unfold h3SobolevFrequencyWeightInv
  apply contDiff_h3SobolevFrequencyWeight.inv
  intro ξ
  exact ne_of_gt (h3SobolevFrequencyWeight_pos ξ)

/-- Complex-valued copy of the reciprocal weight is smooth. -/
theorem contDiff_h3SobolevFrequencyWeightInvComplex :
    ContDiff ℝ ∞ h3SobolevFrequencyWeightInvComplex := by
  unfold h3SobolevFrequencyWeightInvComplex
  exact Complex.ofRealCLM.contDiff.comp
    contDiff_h3SobolevFrequencyWeightInv

/-! ## Compact deweighting -/

/-- Pointwise deweighting of a smooth weighted spectral representative. -/
def h3SmoothCompactDeweighted
    (g : H3FourierPoint3 → ℂ) :
    H3FourierPoint3 → ℂ :=
  fun ξ => h3SobolevFrequencyWeightInvComplex ξ * g ξ

/-- Deweighting preserves compact support. -/
theorem h3SmoothCompactDeweighted_hasCompactSupport
    {g : H3FourierPoint3 → ℂ}
    (hg : HasCompactSupport g) :
    HasCompactSupport (h3SmoothCompactDeweighted g) := by
  apply hg.mono
  simpa [h3SmoothCompactDeweighted] using
    (tsupport_mul_subset_right
      (f := h3SobolevFrequencyWeightInvComplex)
      (g := g))

/-- Deweighting preserves smoothness. -/
theorem h3SmoothCompactDeweighted_contDiff
    {g : H3FourierPoint3 → ℂ}
    (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (h3SmoothCompactDeweighted g) := by
  unfold h3SmoothCompactDeweighted
  exact contDiff_h3SobolevFrequencyWeightInvComplex.mul hg

/-- A smooth compact weighted representative deweights canonically to a Schwartz function. -/
noncomputable def h3SmoothCompactDeweightedSchwartz
    (g : H3FourierPoint3 → ℂ)
    (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ ∞ g) :
    SchwartzMap H3FourierPoint3 ℂ :=
  (h3SmoothCompactDeweighted_hasCompactSupport hcompact).toSchwartzMap
    (h3SmoothCompactDeweighted_contDiff hsmooth)

@[simp]
theorem h3SmoothCompactDeweightedSchwartz_apply
    (g : H3FourierPoint3 → ℂ)
    (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ ∞ g)
    (ξ : H3FourierPoint3) :
    h3SmoothCompactDeweightedSchwartz g hcompact hsmooth ξ
      = h3SobolevFrequencyWeightInvComplex ξ * g ξ :=
  rfl

/-- Exact pointwise cancellation of the H³ weight with its complex reciprocal. -/
theorem h3SobolevFrequencyWeight_mul_invComplex
    (ξ : H3FourierPoint3) :
    (h3SobolevFrequencyWeight ξ : ℂ) *
        h3SobolevFrequencyWeightInvComplex ξ = 1 := by
  have hW : h3SobolevFrequencyWeight ξ ≠ 0 :=
    ne_of_gt (h3SobolevFrequencyWeight_pos ξ)
  unfold h3SobolevFrequencyWeightInvComplex h3SobolevFrequencyWeightInv
  norm_cast
  exact mul_inv_cancel₀ hW

/-- Reweighting the deweighted compact representative returns it pointwise. -/
theorem h3SmoothCompactDeweighted_reweight
    (g : H3FourierPoint3 → ℂ)
    (ξ : H3FourierPoint3) :
    (h3SobolevFrequencyWeight ξ : ℂ) *
        h3SmoothCompactDeweighted g ξ = g ξ := by
  unfold h3SmoothCompactDeweighted
  rw [← mul_assoc, h3SobolevFrequencyWeight_mul_invComplex, one_mul]

/-- Reweighting the canonical deweighted Schwartz representative returns the original
smooth compact weighted representative pointwise. -/
theorem h3SmoothCompactDeweightedSchwartz_reweight
    (g : H3FourierPoint3 → ℂ)
    (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ ∞ g)
    (ξ : H3FourierPoint3) :
    (h3SobolevFrequencyWeight ξ : ℂ) *
        h3SmoothCompactDeweightedSchwartz g hcompact hsmooth ξ = g ξ := by
  rw [h3SmoothCompactDeweightedSchwartz_apply]
  exact h3SmoothCompactDeweighted_reweight g ξ

end

end Euclidean
end Bridge
end PrimeTensor
