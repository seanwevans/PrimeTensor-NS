import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralConvolutionDensity

/-!
# Closure of the weighted H³ convolution by exact Schwartz products

The compact-density theorem gives smooth compact weighted spectral approximants
with an explicit bilinear error bound.  The exact compact anchor identifies the
convolution of every such approximating pair with the weighted Fourier transform
of a genuine Schwartz physical product.

This file closes the epsilon step.  Given arbitrary weighted H³ scalar states
`F`, `G` and any `ε > 0`, we choose one common compact-approximation radius small
enough that the explicit convolution error is strictly below `ε`.  Thus the
genuine weighted H³ product convolution is arbitrarily well approximated in the
bundled weighted `L²` norm by exact Fourier images of Schwartz physical products.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal ContDiff FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralConvolutionClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Arbitrary epsilon form of the compact/Schwartz convolution density passage.
The returned approximants are close to the original inputs, their bundled
weighted convolution is within `ε` of the target, and pointwise that approximant
is exactly the weighted Fourier transform of a Schwartz physical product. -/
theorem exists_h3SmoothCompact_spectralProductAnchor_output_lt
    (F G : H3SpectralScalarState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ,
      0 < δ ∧
      ∃ F' G' : H3SpectralScalarState,
        ∃ f g : H3FourierPoint3 → ℂ,
          ∃ Sf Sg : SchwartzMap H3FourierPoint3 ℂ,
            (F' : H3FourierPoint3 → ℂ) =ᵐ[volume] f ∧
            HasCompactSupport f ∧
            ContDiff ℝ ∞ f ∧
            (G' : H3FourierPoint3 → ℂ) =ᵐ[volume] g ∧
            HasCompactSupport g ∧
            ContDiff ℝ ∞ g ∧
            h3SpectralScalarRawFourier F' =ᵐ[volume] Sf ∧
            h3SpectralScalarRawFourier G' =ᵐ[volume] Sg ∧
            ‖F - F'‖ < δ ∧
            ‖G - G'‖ < δ ∧
            ‖h3WeightedRawProductConvolutionL2 F G -
                h3WeightedRawProductConvolutionL2 F' G'‖ < ε ∧
            ∀ ξ : H3FourierPoint3,
              h3WeightedRawProductConvolution F' G' ξ
                =
              (h3SobolevFrequencyWeight ξ : ℂ) *
                𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
                    (𝓕⁻ Sf) (𝓕⁻ Sg)) ξ := by
  let C : ℝ := 16 * h3SobolevDeweightingConstant
  let S : ℝ := ‖F‖ + ‖G‖ + 1
  let K : ℝ := C * S + 1
  let δ : ℝ := min 1 (ε / (2 * K))

  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) h3SobolevDeweightingConstant_nonneg

  have hS : 0 ≤ S := by
    dsimp [S]
    positivity

  have hK : 0 < K := by
    dsimp [K]
    positivity

  have hFrac : 0 < ε / (2 * K) := by
    exact div_pos hε (mul_pos (by norm_num) hK)

  have hδ : 0 < δ := by
    dsimp [δ]
    rw [lt_min_iff]
    exact ⟨by norm_num, hFrac⟩

  have hδ_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_left _ _

  have hδ_frac : δ ≤ ε / (2 * K) := by
    dsimp [δ]
    exact min_le_right _ _

  have hInner : ‖G‖ + ‖F‖ + δ ≤ S := by
    dsimp [S]
    nlinarith [norm_nonneg F, norm_nonneg G]

  have hErrorLeCS :
      C * δ * ‖G‖ + C * (‖F‖ + δ) * δ
        ≤
      C * δ * S := by
    calc
      C * δ * ‖G‖ + C * (‖F‖ + δ) * δ
          = C * δ * (‖G‖ + ‖F‖ + δ) := by ring
      _ ≤ C * δ * S := by
        exact
          mul_le_mul_of_nonneg_left
            hInner
            (mul_nonneg hC (le_of_lt hδ))

  have hCSLeK : C * S ≤ K := by
    dsimp [K]
    linarith

  have hKFrac : K * (ε / (2 * K)) = ε / 2 := by
    field_simp [ne_of_gt hK]

  have hErrorLt :
      C * δ * ‖G‖ + C * (‖F‖ + δ) * δ < ε := by
    calc
      C * δ * ‖G‖ + C * (‖F‖ + δ) * δ
          ≤ C * δ * S := hErrorLeCS
      _ = (C * S) * δ := by ring
      _ ≤ K * δ := by
        exact mul_le_mul_of_nonneg_right hCSLeK (le_of_lt hδ)
      _ ≤ K * (ε / (2 * K)) := by
        exact mul_le_mul_of_nonneg_left hδ_frac (le_of_lt hK)
      _ = ε / 2 := hKFrac
      _ < ε := by linarith

  obtain ⟨F', G', ⟨f, hF, hfcompact, hfsmooth⟩,
      ⟨g, hG, hgcompact, hgsmooth⟩,
      hFapprox, hGapprox, hConv⟩ :=
    exists_h3SmoothCompact_spectralProductApprox F G hδ

  let Sf : SchwartzMap H3FourierPoint3 ℂ :=
    h3SmoothCompactDeweightedSchwartz f hfcompact hfsmooth
  let Sg : SchwartzMap H3FourierPoint3 ℂ :=
    h3SmoothCompactDeweightedSchwartz g hgcompact hgsmooth

  have hRawF : h3SpectralScalarRawFourier F' =ᵐ[volume] Sf := by
    simpa [Sf] using
      h3SpectralScalarRawFourier_ae_eq_deweightedSchwartz
        F' f hF hfcompact hfsmooth

  have hRawG : h3SpectralScalarRawFourier G' =ᵐ[volume] Sg := by
    simpa [Sg] using
      h3SpectralScalarRawFourier_ae_eq_deweightedSchwartz
        G' g hG hgcompact hgsmooth

  have hConvLt :
      ‖h3WeightedRawProductConvolutionL2 F G -
          h3WeightedRawProductConvolutionL2 F' G'‖ < ε := by
    exact hConv.trans_lt (by simpa [C] using hErrorLt)

  refine ⟨δ, hδ, F', G', f, g, Sf, Sg,
    hF, hfcompact, hfsmooth,
    hG, hgcompact, hgsmooth,
    hRawF, hRawG,
    hFapprox, hGapprox, hConvLt, ?_⟩

  intro ξ
  simpa [Sf, Sg] using
    h3WeightedRawProductConvolution_eq_weighted_fourier_product
      F' G' f g hF hG hfcompact hgcompact hfsmooth hgsmooth ξ

end

end Euclidean
end Bridge
end PrimeTensor
