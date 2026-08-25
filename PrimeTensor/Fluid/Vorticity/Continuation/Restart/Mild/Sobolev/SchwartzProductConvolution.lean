import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayDiffusionFourier
import Mathlib.Analysis.Fourier.Convolution

/-!
# Schwartz product-to-convolution Fourier bridge

The weighted H³ convolution stack constructs the exact candidate frequency
kernel for physical products.  To identify that kernel with the Fourier
transform of an actual physical product, the clean density anchor is the
Schwartz class.

Mathlib already proves the convolution theorem

    𝓕(f ⋆ g) = (𝓕 f) (𝓕 g),

and defines Schwartz convolution by inverse Fourier transform of the pointwise
frequency pairing.  The dual identity needed here is

    𝓕(f g) = (𝓕 f) ⋆ (𝓕 g).

For the unitary real Fourier convention used by Mathlib, Fourier squared is
reflection.  Therefore the dual identity follows algebraically from the
Schwartz convolution definition and the Fourier/inverse-Fourier pair laws,
without any additional integration argument.

This file proves that identity for complex-valued Schwartz functions on the
three-dimensional Fourier carrier.  The next rung can extend it to H³ data by
Schwartz density and the already-proved L² convolution bounds.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- `H3FourierPoint3` is a finite-dimensional Euclidean space.  The defining
module installs this `Fintype` only locally, so recreate it here for the
Schwartz-space instances. -/
noncomputable local instance axisFintypeH3SchwartzProductConvolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On Schwartz functions, applying the Mathlib Fourier transform twice is
reflection. -/
theorem h3Schwartz_fourier_fourier_apply
    (f : SchwartzMap H3FourierPoint3 ℂ)
    (ξ : H3FourierPoint3) :
    𝓕 (𝓕 f) ξ = f (-ξ) := by
  have h := congrArg
    (fun g : SchwartzMap H3FourierPoint3 ℂ => g (-ξ))
    (FourierTransform.fourierInv_fourier_eq (E := SchwartzMap H3FourierPoint3 ℂ) (F := SchwartzMap H3FourierPoint3 ℂ) f)
  rw [SchwartzMap.fourierInv_apply_eq] at h
  simpa using h

/-- The pointwise product pairing of the reflected Fourier-squared inputs is
exactly the Fourier square of the pointwise product. -/
theorem h3Schwartz_pairing_fourier_fourier_eq
    (f g : SchwartzMap H3FourierPoint3 ℂ) :
    SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
        (𝓕 (𝓕 f)) (𝓕 (𝓕 g))
      =
    𝓕 (𝓕 (SchwartzMap.pairing
      (ContinuousLinearMap.mul ℂ ℂ) f g)) := by
  ext ξ
  simp only [SchwartzMap.pairing_apply_apply]
  rw [h3Schwartz_fourier_fourier_apply f ξ]
  rw [h3Schwartz_fourier_fourier_apply g ξ]
  rw [h3Schwartz_fourier_fourier_apply
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) ξ]
  rfl

/-- Fourier transform takes a Schwartz pointwise product to the Schwartz
convolution of the two Fourier transforms. -/
theorem h3Schwartz_fourier_product_eq_convolution
    (f g : SchwartzMap H3FourierPoint3 ℂ) :
    𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g)
      =
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (𝓕 f) (𝓕 g) := by
  change
    𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g)
      =
    𝓕⁻ (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
      (𝓕 (𝓕 f)) (𝓕 (𝓕 g)))
  rw [h3Schwartz_pairing_fourier_fourier_eq f g]
  rw [FourierTransform.fourierInv_fourier_eq (E := SchwartzMap H3FourierPoint3 ℂ) (F := SchwartzMap H3FourierPoint3 ℂ)]

/-- Pointwise form of the Schwartz product-to-convolution identity. -/
theorem h3Schwartz_fourier_product_apply_eq_convolution
    (f g : SchwartzMap H3FourierPoint3 ℂ)
    (ξ : H3FourierPoint3) :
    𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) ξ
      =
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (𝓕 f) (𝓕 g) ξ := by
  rw [h3Schwartz_fourier_product_eq_convolution f g]

end

end Euclidean
end Bridge
end PrimeTensor
