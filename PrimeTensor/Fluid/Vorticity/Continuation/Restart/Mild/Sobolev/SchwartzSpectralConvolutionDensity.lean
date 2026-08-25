import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralConvolutionAnchor
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralCompactDensity

/-!
# Density passage for the weighted H³ product convolution

The exact compact/Schwartz anchor identifies the genuine weighted convolution of
smooth compact spectral approximants with the weighted Fourier transform of an
actual Schwartz physical product.  `WeightedConvolutionDifference` supplies the
quantitative continuity estimate needed to pass from those anchors back toward
arbitrary weighted H³ spectral states.

This file packages the two ingredients in one approximation theorem.  For every
positive approximation radius `δ`, both inputs admit smooth compact weighted
approximants whose exact product is a Schwartz product/convolution anchor, while
the resulting bundled weighted convolution differs from the target by an
explicit quantity tending to zero with `δ`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal ContDiff FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralConvolutionDensity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Quantitative convolution error when both weighted spectral inputs are
approximated within the same radius `δ`. -/
theorem norm_h3WeightedRawProductConvolutionL2_sub_le_of_approx
    (F G F' G' : H3SpectralScalarState)
    {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hF : ‖F - F'‖ ≤ δ)
    (hG : ‖G - G'‖ ≤ δ) :
    ‖h3WeightedRawProductConvolutionL2 F G -
        h3WeightedRawProductConvolutionL2 F' G'‖
      ≤
    (16 * h3SobolevDeweightingConstant) * δ * ‖G‖ +
      (16 * h3SobolevDeweightingConstant) * (‖F‖ + δ) * δ := by
  have hC : 0 ≤ 16 * h3SobolevDeweightingConstant := by
    exact mul_nonneg (by norm_num) h3SobolevDeweightingConstant_nonneg

  have hF'norm : ‖F'‖ ≤ ‖F‖ + δ := by
    calc
      ‖F'‖ = ‖F - (F - F')‖ := by
        congr 1
        abel
      _ ≤ ‖F‖ + ‖F - F'‖ := norm_sub_le _ _
      _ ≤ ‖F‖ + δ := add_le_add (le_refl ‖F‖) hF

  have hFirst :
      (16 * h3SobolevDeweightingConstant) * ‖F - F'‖ * ‖G‖
        ≤
      (16 * h3SobolevDeweightingConstant) * δ * ‖G‖ := by
    exact
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hF hC)
        (norm_nonneg G)

  have hSecondNorm :
      (16 * h3SobolevDeweightingConstant) * ‖F'‖
        ≤
      (16 * h3SobolevDeweightingConstant) * (‖F‖ + δ) := by
    exact mul_le_mul_of_nonneg_left hF'norm hC

  have hSecond :
      (16 * h3SobolevDeweightingConstant) * ‖F'‖ * ‖G - G'‖
        ≤
      (16 * h3SobolevDeweightingConstant) * (‖F‖ + δ) * δ := by
    calc
      (16 * h3SobolevDeweightingConstant) * ‖F'‖ * ‖G - G'‖
          ≤
        (16 * h3SobolevDeweightingConstant) * (‖F‖ + δ) * ‖G - G'‖ := by
            exact
              mul_le_mul_of_nonneg_right
                hSecondNorm
                (norm_nonneg (G - G'))
      _ ≤
        (16 * h3SobolevDeweightingConstant) * (‖F‖ + δ) * δ := by
            exact
              mul_le_mul_of_nonneg_left
                hG
                (mul_nonneg hC (add_nonneg (norm_nonneg F) hδ))

  exact
    (norm_h3WeightedRawProductConvolutionL2_sub_le F F' G G').trans
      (add_le_add hFirst hSecond)

/-- Every pair of weighted H³ scalar states admits smooth compact spectral
approximants satisfying the hypotheses of the exact Schwartz convolution anchor,
with a quantitative bundled weighted-convolution error bound. -/
theorem exists_h3SmoothCompact_spectralProductApprox
    (F G : H3SpectralScalarState)
    {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ F' G' : H3SpectralScalarState,
      (∃ f : H3FourierPoint3 → ℂ,
        (F' : H3FourierPoint3 → ℂ) =ᵐ[volume] f ∧
        HasCompactSupport f ∧
        ContDiff ℝ ∞ f) ∧
      (∃ g : H3FourierPoint3 → ℂ,
        (G' : H3FourierPoint3 → ℂ) =ᵐ[volume] g ∧
        HasCompactSupport g ∧
        ContDiff ℝ ∞ g) ∧
      ‖F - F'‖ < δ ∧
      ‖G - G'‖ < δ ∧
      ‖h3WeightedRawProductConvolutionL2 F G -
          h3WeightedRawProductConvolutionL2 F' G'‖
        ≤
      (16 * h3SobolevDeweightingConstant) * δ * ‖G‖ +
        (16 * h3SobolevDeweightingConstant) * (‖F‖ + δ) * δ := by
  obtain ⟨F', hFcompact, hFapprox⟩ :=
    exists_h3SmoothCompact_spectralApprox_norm F hδ
  obtain ⟨G', hGcompact, hGapprox⟩ :=
    exists_h3SmoothCompact_spectralApprox_norm G hδ

  refine ⟨F', G', hFcompact, hGcompact, hFapprox, hGapprox, ?_⟩
  exact
    norm_h3WeightedRawProductConvolutionL2_sub_le_of_approx
      F G F' G' (le_of_lt hδ) (le_of_lt hFapprox) (le_of_lt hGapprox)

end

end Euclidean
end Bridge
end PrimeTensor
