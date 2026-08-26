import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Product.Convolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weighted.Convolution.Pointwise

/-!
# Schwartz product convolution in the exact PrimeTensor kernel orientation

`SchwartzProductConvolution` proves the abstract Schwartz identity

    𝓕(f g) = (𝓕 f) ⋆ (𝓕 g).

Mathlib's function-level convolution is defined in exactly the orientation
used by the H³ spectral solver:

    ∫ η, f(η) g(ξ - η).

This file unfolds that definition explicitly and then multiplies by the exact
H³ frequency weight.  The terminal formula is therefore literally
the scalar kernel appearing in `h3WeightedRawProductConvolution`, with the raw
spectral amplitudes specialized to Fourier transforms of Schwartz functions.

No density or limiting argument is used yet; this is the exact smooth anchor
for the later H³ extension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzProductConvolutionKernel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Raw product convolution of two Schwartz Fourier amplitudes, written in the
same orientation as the H³ spectral solver. -/
noncomputable def h3SchwartzRawProductConvolution
    (f g : SchwartzMap H3FourierPoint3 ℂ)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ η : H3FourierPoint3,
    𝓕 f η * 𝓕 g (ξ - η)

/-- Mathlib's Schwartz convolution orientation agrees with PrimeTensor's raw
product-kernel orientation. -/
theorem h3Schwartz_convolution_apply_eq_rawProductConvolution
    (f g : SchwartzMap H3FourierPoint3 ℂ)
    (ξ : H3FourierPoint3) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (𝓕 f) (𝓕 g) ξ
      =
    h3SchwartzRawProductConvolution f g ξ := by
  rw [SchwartzMap.convolution_apply]
  unfold MeasureTheory.convolution h3SchwartzRawProductConvolution
  simp only [ContinuousLinearMap.mul_apply']

/-- Pointwise Fourier transform of a Schwartz product is exactly the raw
PrimeTensor convolution kernel. -/
theorem h3Schwartz_fourier_product_apply_eq_rawProductConvolution
    (f g : SchwartzMap H3FourierPoint3 ℂ)
    (ξ : H3FourierPoint3) :
    𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) ξ
      =
    h3SchwartzRawProductConvolution f g ξ := by
  rw [h3Schwartz_fourier_product_apply_eq_convolution]
  exact h3Schwartz_convolution_apply_eq_rawProductConvolution f g ξ

/-- Weighted Schwartz product convolution, in exactly the form used by the H³
spectral scalar product operator. -/
noncomputable def h3SchwartzWeightedProductConvolution
    (f g : SchwartzMap H3FourierPoint3 ℂ)
    (ξ : H3FourierPoint3) : ℂ :=
  (h3SobolevFrequencyWeight ξ : ℂ) *
    h3SchwartzRawProductConvolution f g ξ

/-- Multiplying the Schwartz product Fourier identity by the exact H³ weight
produces the exact weighted nonlinear kernel used by the solver. -/
theorem h3Schwartz_weighted_fourier_product_apply_eq_convolution
    (f g : SchwartzMap H3FourierPoint3 ℂ)
    (ξ : H3FourierPoint3) :
    (h3SobolevFrequencyWeight ξ : ℂ) *
        𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) ξ
      =
    h3SchwartzWeightedProductConvolution f g ξ := by
  unfold h3SchwartzWeightedProductConvolution
  rw [h3Schwartz_fourier_product_apply_eq_rawProductConvolution]

end

end Euclidean
end Bridge
end PrimeTensor
