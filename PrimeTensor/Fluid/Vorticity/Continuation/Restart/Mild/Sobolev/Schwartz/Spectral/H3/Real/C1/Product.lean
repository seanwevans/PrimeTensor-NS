import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Raw.Outer.Divergence.Physical.Product.Derivative.Bridge
import Mathlib.Analysis.Fourier.Convolution

/-!
# Exact pointwise reconstruction of the H³ spectral product

For arbitrary weighted H³ scalar states `F` and `G`, the deweighted raw Fourier
amplitudes belong to `L¹`.  PrimeTensor's raw nonlinear product is their exact
convolution,

    rawConv(F,G) = f̂ * ĝ,

and the bundled weighted H³ product state deweights almost everywhere to that
same convolution.

Mathlib's Fourier convolution theorem therefore applies directly.  Since the
project's ordinary inverse Fourier transform is the forward Fourier transform
evaluated at `-x`, it gives the exact pointwise identity

    C1Rep(weightedRawProduct F G)(x)
      = C1Rep(F)(x) * C1Rep(G)(x).

This is stronger than the earlier physical `L²` closure theorem: no density
limit remains in the statement.  No new estimate is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal FourierTransform Convolution

noncomputable section

noncomputable local instance axisFintypeH3C1ProductReconstruction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- PrimeTensor's raw H³ product convolution is exactly Mathlib's ordinary
bilinear convolution with complex multiplication. -/
theorem h3RawProductConvolution_eq_measureTheory_convolution
    (F G : H3SpectralScalarState) :
    h3RawProductConvolution F G
      =
    (h3SpectralScalarRawFourier F
      ⋆[ContinuousLinearMap.mul ℂ ℂ]
      h3SpectralScalarRawFourier G) := by
  funext ξ
  unfold h3RawProductConvolution MeasureTheory.convolution
  simp only [ContinuousLinearMap.mul_apply']

/-- Exact complex pointwise product reconstruction for the bundled weighted
H³ spectral convolution. -/
theorem h3SpectralScalarC1Representative_weightedRawProductConvolutionL2_eq_mul
    (F G : H3SpectralScalarState)
    (x : H3FourierPoint3) :
    h3SpectralScalarC1Representative
        (h3WeightedRawProductConvolutionL2 F G)
        x
      =
    h3SpectralScalarC1Representative F x *
      h3SpectralScalarC1Representative G x := by
  let H : H3SpectralScalarState :=
    h3WeightedRawProductConvolutionL2 F G

  have hRaw :
      h3SpectralScalarRawFourier H
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawProductConvolution F G := by
    dsimp only [H]
    exact
      h3SpectralScalarRawFourier_weightedRawProductConvolutionL2_ae
        F G

  have hFInt :
      Integrable
        (h3SpectralScalarRawFourier F)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 F)

  have hGInt :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  unfold h3SpectralScalarC1Representative

  simp_rw [Real.fourierInv_eq_fourier_neg]

  calc
    FourierTransform.fourier
        (h3SpectralScalarRawFourier H)
        (-x)
        =
      FourierTransform.fourier
        (h3RawProductConvolution F G)
        (-x) :=
      Real.fourier_congr_ae hRaw (-x)
    _ =
      FourierTransform.fourier
          (h3SpectralScalarRawFourier F)
          (-x)
        *
      FourierTransform.fourier
          (h3SpectralScalarRawFourier G)
          (-x) := by
      rw [h3RawProductConvolution_eq_measureTheory_convolution]
      exact
        Real.fourier_mul_convolution_eq
          hFInt hGInt (-x)

/-- If the two complex representatives are real at a point, taking real parts
of the exact complex product reconstruction gives the corresponding real
pointwise product. -/
theorem h3SpectralScalarRealC1Representative_weightedRawProductConvolutionL2_eq_mul_of_im_eq_zero
    (F G : H3SpectralScalarState)
    (x : H3FourierPoint3)
    (hFim :
      (h3SpectralScalarC1Representative F x).im = 0)
    (hGim :
      (h3SpectralScalarC1Representative G x).im = 0) :
    h3SpectralScalarRealC1Representative
        (h3WeightedRawProductConvolutionL2 F G)
        x
      =
    h3SpectralScalarRealC1Representative F x *
      h3SpectralScalarRealC1Representative G x := by
  unfold h3SpectralScalarRealC1Representative

  rw [
    h3SpectralScalarC1Representative_weightedRawProductConvolutionL2_eq_mul
  ]

  simp only [Complex.mul_re, hFim, hGim, zero_mul, sub_zero]

end

end Euclidean
end Bridge
end PrimeTensor
