import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Convolution.Closure
import Mathlib.Analysis.Fourier.Convolution

/-!
# BKM endpoint: exact dyadic Schwartz convolution anchor

The density closure theorem reduces the endpoint `L¹ * L²` Fourier bridge to a
single smooth anchor.  This file isolates the purely Schwartz part of that
anchor.

For one dyadic BKM kernel

    Kᵢₖ,R = 𝓕⁻ Mᵢₖ,R,

and one Schwartz input `P`, define the Schwartz convolution

    Kᵢₖ,R * P.

Mathlib's Schwartz convolution theorem gives

    𝓕(Kᵢₖ,R * P)
      = (𝓕Kᵢₖ,R) (𝓕P)
      = Mᵢₖ,R (𝓕P).

We record this first pointwise in Schwartz space and then as an exact equality
of bundled Fourier `L²` states.  The latter has exactly the same right-hand
side as `DyadicConvolutionClosure`.

The only remaining bridge after this file is therefore to identify the
project's endpoint Bochner convolution

    h3L1L2Convolution (Kᵢₖ,R : L¹) (P : L²)

with the `L²` package of this Schwartz convolution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open FourierTransform
open scoped ENNReal NNReal Convolution

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicSchwartzAnchor
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact Schwartz convolution of one dyadic BKM kernel with `P`. -/
noncomputable def h3BKMDyadicSchwartzConvolution
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3)
    (P : SchwartzMap H3FourierPoint3 ℂ) :
    SchwartzMap H3FourierPoint3 ℂ :=
  SchwartzMap.convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (h3BKMDyadicKernelSchwartz R hR i k)
    P

/--
The dyadic Schwartz convolution has exactly the scalar kernel orientation used
by the endpoint Young construction.
-/
theorem h3BKMDyadicSchwartzConvolution_apply
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (P : SchwartzMap H3FourierPoint3 ℂ)
    (ξ : H3FourierPoint3) :
    h3BKMDyadicSchwartzConvolution
        R hR i k P ξ
      =
    ∫ η : H3FourierPoint3,
      h3BKMDyadicKernel R hR i k η
        *
      P (ξ - η) := by

  unfold h3BKMDyadicSchwartzConvolution

  rw [SchwartzMap.convolution_apply]

  unfold MeasureTheory.convolution
  unfold h3BKMDyadicKernel

  simp only [ContinuousLinearMap.mul_apply']

/--
Pointwise Schwartz Fourier identity for one dyadic BKM convolution.
-/
theorem h3BKMDyadicSchwartzConvolution_fourier_apply
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (P : SchwartzMap H3FourierPoint3 ℂ)
    (ξ : H3FourierPoint3) :
    𝓕 (h3BKMDyadicSchwartzConvolution
        R hR i k P) ξ
      =
    h3BKMLocalizedCoordinateMultiplier
        R hR i k ξ
      *
    𝓕 P ξ := by

  unfold h3BKMDyadicSchwartzConvolution

  rw [SchwartzMap.fourier_convolution]

  simp only [
    SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply'
  ]

  unfold h3BKMDyadicKernelSchwartz

  rw [FourierTransform.fourier_fourierInv_eq]

  rw [
    h3BKMLocalizedCoordinateMultiplierSchwartz_apply
      hR i k ξ
  ]

/--
Bundled `L²` form of the dyadic Schwartz Fourier identity.

The right-hand side is exactly the localization operator used by the density
closure theorem.
-/
theorem h3BKMDyadicSchwartzConvolutionL2_fourier_eq_localized
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (P : SchwartzMap H3FourierPoint3 ℂ) :
    (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      ((h3BKMDyadicSchwartzConvolution
          R hR i k P).toLp
        2
        (volume : Measure H3FourierPoint3))
      =
    h3BKMLocalizedCoordinateMultiplierApplyL2
      R hR i k
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
        (P.toLp
          2
          (volume : Measure H3FourierPoint3))) := by

  change
    𝓕 ((h3BKMDyadicSchwartzConvolution
          R hR i k P).toLp
        2
        (volume : Measure H3FourierPoint3))
      =
    h3BKMLocalizedCoordinateMultiplierApplyL2
      R hR i k
      (𝓕 (P.toLp
        2
        (volume : Measure H3FourierPoint3)))

  simp only [SchwartzMap.toLp_fourier_eq]

  apply MeasureTheory.Lp.ext

  filter_upwards [
    SchwartzMap.coeFn_toLp
      (𝓕 (h3BKMDyadicSchwartzConvolution
        R hR i k P) :
        SchwartzMap H3FourierPoint3 ℂ)
      2
      (volume : Measure H3FourierPoint3),
    h3BKMLocalizedCoordinateMultiplierApplyL2_ae
      hR i k
      ((𝓕 P : SchwartzMap H3FourierPoint3 ℂ).toLp
        2
        (volume : Measure H3FourierPoint3)),
    SchwartzMap.coeFn_toLp
      (𝓕 P : SchwartzMap H3FourierPoint3 ℂ)
      2
      (volume : Measure H3FourierPoint3)
  ] with ξ hLeft hLocalized hP

  rw [hLeft, hLocalized, hP]

  exact
    h3BKMDyadicSchwartzConvolution_fourier_apply
      hR i k P ξ

end

end Euclidean
end Bridge
end PrimeTensor
