import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralConvolutionClosedTransfer
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralConvolutionReality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralRealizabilityClosure

/-!
# Physical L² closure of the weighted H³ product convolution

`SchwartzSpectralConvolutionClosedTransfer` shows that every genuine weighted
H³ convolution is a norm limit of exact spectral anchors coming from Schwartz
physical products.  This file pushes that closure statement through the exact
complex inverse-Fourier decoder.

The first lemma identifies the decoder of one exact spectral anchor with the
`L²` class of the corresponding pointwise Schwartz product.  Since the decoder
is contractive from the weighted H³ spectral norm to physical `L²`, the spectral
anchor approximation immediately becomes a physical `L²` approximation.

Thus the decoded nonlinear product of arbitrary weighted H³ inputs belongs to
the `L²` closure of genuine pointwise Schwartz products.  This is the physical
product-realization statement needed before identifying the spectral mild
nonlinearity with the physical Navier--Stokes product.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal ContDiff FourierTransform Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralConvolutionPhysicalClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A complex physical `L²` state is an exact Schwartz-product anchor when it
is the `L²` class of the pointwise product of two Schwartz functions.  The two
Schwartz factors are written as inverse Fourier transforms because that is the
canonical form supplied by the spectral anchor theorem. -/
def H3SchwartzPhysicalProductL2Anchor
    (u : H3ComplexPhysicalScalarL2) : Prop :=
  ∃ Sf Sg : SchwartzMap H3FourierPoint3 ℂ,
    u =
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
          (𝓕⁻ Sf) (𝓕⁻ Sg)).toLp 2 volume

/-- Decoding one exact spectral Schwartz-product anchor gives exactly the
physical `L²` class of the associated pointwise Schwartz product. -/
theorem h3SchwartzProductSpectralAnchor_decodeComplexL2
    {H : H3SpectralScalarState}
    (hH : H3SchwartzProductSpectralAnchor H) :
    H3SchwartzPhysicalProductL2Anchor
      (h3SpectralScalarDecodeComplexL2 H) := by
  rcases hH with
    ⟨F', G', f, g, Sf, Sg,
      hF, hfcompact, hfsmooth,
      hG, hgcompact, hgsmooth,
      hH, hExact⟩

  subst H

  let P : SchwartzMap H3FourierPoint3 ℂ :=
    SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
      (𝓕⁻ Sf) (𝓕⁻ Sg)

  refine ⟨Sf, Sg, ?_⟩
  change
    h3SpectralScalarDecodeComplexL2
        (h3WeightedRawProductConvolutionL2 F' G')
      = P.toLp 2 volume

  apply
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).injective

  rw [h3Fourier_h3SpectralScalarDecodeComplexL2]
  change
    h3SpectralScalarRawFourierL2
        (h3WeightedRawProductConvolutionL2 F' G')
      =
    𝓕 (P.toLp 2 volume)
  rw [SchwartzMap.toLp_fourier_eq]

  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_weightedRawProductConvolutionL2_ae F' G',
    SchwartzMap.coeFn_toLp (𝓕 P) 2 volume
  ] with ξ hRaw hFourier

  rw [hRaw, hFourier]

  have hWeighted :
      (h3SobolevFrequencyWeight ξ : ℂ) *
          h3RawProductConvolution F' G' ξ
        =
      (h3SobolevFrequencyWeight ξ : ℂ) * 𝓕 P ξ := by
    simpa [P, h3WeightedRawProductConvolution] using hExact ξ

  have hWReal : h3SobolevFrequencyWeight ξ ≠ 0 :=
    ne_of_gt (h3SobolevFrequencyWeight_pos ξ)
  have hW : (h3SobolevFrequencyWeight ξ : ℂ) ≠ 0 := by
    exact_mod_cast hWReal

  exact mul_left_cancel₀ hW hWeighted

/-- The exact complex spectral decoder is a contraction from the weighted H³
spectral norm to physical `L²`, also in two-point distance form. -/
theorem dist_h3SpectralScalarDecodeComplexL2_le
    (F G : H3SpectralScalarState) :
    dist (h3SpectralScalarDecodeComplexL2 F)
        (h3SpectralScalarDecodeComplexL2 G)
      ≤ dist F G := by
  simp only [dist_eq_norm]
  rw [← h3SpectralScalarDecodeComplexL2_sub]
  exact norm_h3SpectralScalarDecodeComplexL2_le (F - G)

/-- Epsilon form of physical product realization: the decoded genuine weighted
H³ convolution is arbitrarily close in physical `L²` to an actual pointwise
Schwartz product. -/
theorem exists_h3SchwartzPhysicalProductL2Anchor_dist_lt
    (F G : H3SpectralScalarState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ u : H3ComplexPhysicalScalarL2,
      H3SchwartzPhysicalProductL2Anchor u ∧
      dist
        (h3SpectralScalarDecodeComplexL2
          (h3WeightedRawProductConvolutionL2 F G))
        u < ε := by
  obtain ⟨H, hAnchor, hDist⟩ :=
    exists_h3SchwartzProductSpectralAnchor_dist_lt F G hε

  have hPhysical :
      H3SchwartzPhysicalProductL2Anchor
        (h3SpectralScalarDecodeComplexL2 H) :=
    h3SchwartzProductSpectralAnchor_decodeComplexL2 hAnchor

  refine ⟨h3SpectralScalarDecodeComplexL2 H, hPhysical, ?_⟩
  exact
    (dist_h3SpectralScalarDecodeComplexL2_le
      (h3WeightedRawProductConvolutionL2 F G) H).trans_lt hDist

/-- The decoded genuine weighted H³ convolution lies in the physical `L²`
closure of exact pointwise Schwartz products. -/
theorem h3SpectralScalarDecodeComplexL2_weightedRawProductConvolutionL2_mem_closure
    (F G : H3SpectralScalarState) :
    h3SpectralScalarDecodeComplexL2
        (h3WeightedRawProductConvolutionL2 F G)
      ∈ closure
        {u : H3ComplexPhysicalScalarL2 |
          H3SchwartzPhysicalProductL2Anchor u} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨u, hAnchor, hDist⟩ :=
    exists_h3SchwartzPhysicalProductL2Anchor_dist_lt F G hε
  exact ⟨u, hAnchor, hDist⟩

end

end Euclidean
end Bridge
end PrimeTensor
