import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.WeightedConvolutionIntegrand
import Mathlib.Analysis.Convolution

/-!
# Pointwise scalar assembly for the weighted H³ convolution

The fixed-`η` weighted kernel from `WeightedConvolutionIntegrand` belongs to `L²` in the
output frequency, but the resulting `L²`-valued map of `η` need not be Bochner integrable under
only H³ data.  The correct endpoint argument therefore returns to the scalar convolution integral.

For fixed output frequency `ξ`, both raw factors lie in `L²` as functions of `η`, including the
reflected translate `η ↦ ĝ (ξ - η)`.  Hölder then gives scalar integrability of

    η ↦ f̂(η) * ĝ(ξ - η).

This file records that pointwise integrability and the exact change of variables that swaps the
first Sobolev-weight majorant into the `L¹ * L²` orientation used by `YoungConvolution`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3WeightedConvolutionPointwise
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Reflection about `ξ`, namely `η ↦ ξ - η`, preserves Fourier volume. -/
theorem h3MeasurePreserving_sub_left
    (ξ : H3FourierPoint3) :
    MeasurePreserving
      (fun η : H3FourierPoint3 => ξ - η)
      (volume : Measure H3FourierPoint3)
      (volume : Measure H3FourierPoint3) := by
  exact
    (volume : Measure H3FourierPoint3).measurePreserving_sub_left ξ

/-- A reflected translate of a raw Fourier amplitude remains in `L²`. -/
theorem h3SpectralScalarRawFourier_reflectedShift_memLp2
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    MemLp
      (fun η : H3FourierPoint3 =>
        h3SpectralScalarRawFourier G (ξ - η))
      2
      (volume : Measure H3FourierPoint3) := by
  exact
    (h3SpectralScalarRawFourier_memLp2 G).comp_measurePreserving
      (h3MeasurePreserving_sub_left ξ)

/-- A reflected translate of a weighted spectral state remains in `L²`. -/
theorem h3SpectralScalarState_reflectedShift_memLp2
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    MemLp
      (fun η : H3FourierPoint3 => G (ξ - η))
      2
      (volume : Measure H3FourierPoint3) := by
  exact
    (MeasureTheory.Lp.memLp G).comp_measurePreserving
      (h3MeasurePreserving_sub_left ξ)

/-- The genuine scalar raw convolution kernel is integrable for every output frequency. -/
theorem h3RawProductKernel_integrable
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    Integrable
      (fun η : H3FourierPoint3 =>
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η))
      (volume : Measure H3FourierPoint3) := by
  rw [← memLp_one_iff_integrable]
  simpa only [mul_comm] using
    (h3SpectralScalarRawFourier_memLp2 F).mul'
      (r := (1 : ENNReal))
      (h3SpectralScalarRawFourier_reflectedShift_memLp2 G ξ)

/-- The genuinely weighted scalar kernel is also integrable at each output frequency. -/
theorem h3WeightedRawProductKernel_pointwise_integrable
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    Integrable
      (fun η : H3FourierPoint3 =>
        h3WeightedRawProductKernelAt F G η ξ)
      (volume : Measure H3FourierPoint3) := by
  simpa [h3WeightedRawProductKernelAt] using
    (h3RawProductKernel_integrable F G ξ).const_mul
      (h3SobolevFrequencyWeight ξ : ℂ)

/-- The scalar raw convolution represented by the exact PDE Fourier kernel. -/
noncomputable def h3RawProductConvolution
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ η : H3FourierPoint3,
    h3SpectralScalarRawFourier F η *
      h3SpectralScalarRawFourier G (ξ - η)

/-- The exact weighted scalar convolution. -/
noncomputable def h3WeightedRawProductConvolution
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℂ :=
  (h3SobolevFrequencyWeight ξ : ℂ) *
    h3RawProductConvolution F G ξ

/-- The weighted scalar convolution is exactly the integral of the true weighted kernel. -/
theorem h3WeightedRawProductConvolution_eq_integral
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3WeightedRawProductConvolution F G ξ
      =
    ∫ η : H3FourierPoint3,
      h3WeightedRawProductKernelAt F G η ξ := by
  unfold
    h3WeightedRawProductConvolution
    h3RawProductConvolution
    h3WeightedRawProductKernelAt
  rw [integral_const_mul]

/--
The first Sobolev majorant has the exact reflected change-of-variables form needed to orient it as
`L¹ * L²`: the raw `G` factor moves into the integration slot and the weighted `F` factor becomes
the translated `L²` state.
-/
theorem h3FirstYoungMajorant_swap
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    (∫ η : H3FourierPoint3,
        ‖F η‖ *
          ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      =
    ∫ η : H3FourierPoint3,
      ‖h3SpectralScalarRawFourier G η‖ *
        ‖F (ξ - η)‖ := by
  rw [← integral_sub_left_eq_self
    (fun η : H3FourierPoint3 =>
      ‖h3SpectralScalarRawFourier G η‖ * ‖F (ξ - η)‖)
    (volume : Measure H3FourierPoint3)
    ξ]
  simp_rw [sub_sub_self]
  simpa only [mul_comm]

end

end Euclidean
end Bridge
end PrimeTensor
