import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.RawFourierL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.YoungConvolutionRepresentatives
import Mathlib.MeasureTheory.Group.Integral

/-!
# The exact weighted H³ convolution kernel as an L² state

For weighted spectral states `F = W₃ f̂` and `G = W₃ ĝ`, the Fourier-side
H³ product kernel at integration parameter `η` is

    ξ ↦ W₃(ξ) * f̂(η) * ĝ(ξ - η).

The previous Sobolev algebra module proves the exact pointwise estimate

    W₃(ξ) |f̂(η) ĝ(ξ-η)|
      ≤ 8 (|F(η)| |ĝ(ξ-η)| + |f̂(η)| |G(ξ-η)|).

For fixed `η`, both translated factors on the right remain in `L²` because
Lebesgue volume is translation invariant.  Hence the right-hand side is an
`L²` majorant, and the true weighted kernel belongs to `L²`.

This file packages that fixed-`η` kernel as an actual `H3FourierComplexL2`
state.  It does not yet integrate in `η`; the next step is to prove the
resulting `L²`-valued map is Bochner integrable with the quantitative Sobolev
algebra bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3WeightedConvolutionIntegrand
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact weighted raw product kernel at fixed convolution parameter `η`. -/
def h3WeightedRawProductKernelAt
    (F G : H3SpectralScalarState)
    (η ξ : H3FourierPoint3) : ℂ :=
  (h3SobolevFrequencyWeight ξ : ℂ) *
    (h3SpectralScalarRawFourier F η *
      h3SpectralScalarRawFourier G (ξ - η))

/-- The previously proved exact Sobolev weight split, in the fixed-`η` notation. -/
theorem norm_h3WeightedRawProductKernelAt_le
    (F G : H3SpectralScalarState)
    (η ξ : H3FourierPoint3) :
    ‖h3WeightedRawProductKernelAt F G η ξ‖
      ≤
    8 *
      (‖F η‖ *
          ‖h3SpectralScalarRawFourier G (ξ - η)‖
        +
       ‖h3SpectralScalarRawFourier F η‖ *
          ‖G (ξ - η)‖) := by
  simpa [h3WeightedRawProductKernelAt] using
    norm_h3WeightedRawProductKernel_le F G ξ η

/-- Translation by `ξ ↦ ξ - η` preserves Fourier volume. -/
theorem h3MeasurePreserving_sub_right
    (η : H3FourierPoint3) :
    MeasurePreserving
      (fun ξ : H3FourierPoint3 => ξ - η)
      (volume : Measure H3FourierPoint3)
      (volume : Measure H3FourierPoint3) := by
  simpa [sub_eq_add_neg] using
    (measurePreserving_add_right
      (volume : Measure H3FourierPoint3)
      (-η))

/-- The translated raw Fourier amplitude remains in `L²`. -/
theorem h3SpectralScalarRawFourier_shift_memLp2
    (G : H3SpectralScalarState)
    (η : H3FourierPoint3) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier G (ξ - η))
      2
      (volume : Measure H3FourierPoint3) := by
  exact
    (h3SpectralScalarRawFourier_memLp2 G).comp_measurePreserving
      (h3MeasurePreserving_sub_right η)

/-- A weighted spectral state itself remains `L²` after translation. -/
theorem h3SpectralScalarState_shift_memLp2
    (G : H3SpectralScalarState)
    (η : H3FourierPoint3) :
    MemLp
      (fun ξ : H3FourierPoint3 => G (ξ - η))
      2
      (volume : Measure H3FourierPoint3) := by
  exact
    (MeasureTheory.Lp.memLp G).comp_measurePreserving
      (h3MeasurePreserving_sub_right η)

/-- The true weighted raw product kernel is a.e. strongly measurable. -/
theorem h3WeightedRawProductKernelAt_aestronglyMeasurable
    (F G : H3SpectralScalarState)
    (η : H3FourierPoint3) :
    AEStronglyMeasurable
      (h3WeightedRawProductKernelAt F G η)
      (volume : Measure H3FourierPoint3) := by
  have hW :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          (h3SobolevFrequencyWeight ξ : ℂ))
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp
      continuous_h3SobolevFrequencyWeight).aestronglyMeasurable

  have hRawShift :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3SpectralScalarRawFourier G (ξ - η))
        (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourier_shift_memLp2 G η).1

  unfold h3WeightedRawProductKernelAt
  exact
    hW.mul
      (aestronglyMeasurable_const.mul hRawShift)

/--
For fixed `η`, the exact weighted product kernel belongs to Fourier `L²`.

The proof uses the exact weight split only as a pointwise majorant; the kernel
itself is unchanged.
-/
theorem h3WeightedRawProductKernelAt_memLp2
    (F G : H3SpectralScalarState)
    (η : H3FourierPoint3) :
    MemLp
      (h3WeightedRawProductKernelAt F G η)
      2
      (volume : Measure H3FourierPoint3) := by
  have hRawShift :=
    h3SpectralScalarRawFourier_shift_memLp2 G η

  have hGShift :=
    h3SpectralScalarState_shift_memLp2 G η

  have hDomLeft :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ‖F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖)
        2
        (volume : Measure H3FourierPoint3) :=
    hRawShift.norm.const_mul ‖F η‖

  have hDomRight :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖G (ξ - η)‖)
        2
        (volume : Measure H3FourierPoint3) :=
    hGShift.norm.const_mul
      ‖h3SpectralScalarRawFourier F η‖

  have hDom :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          8 *
            (‖F η‖ *
                ‖h3SpectralScalarRawFourier G (ξ - η)‖
              +
             ‖h3SpectralScalarRawFourier F η‖ *
                ‖G (ξ - η)‖))
        2
        (volume : Measure H3FourierPoint3) :=
    (hDomLeft.add hDomRight).const_mul (8 : ℝ)

  apply
    hDom.of_le
      (h3WeightedRawProductKernelAt_aestronglyMeasurable F G η)

  filter_upwards with ξ

  have hSumNonneg :
      0 ≤
        ‖F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖
          +
        ‖h3SpectralScalarRawFourier F η‖ *
            ‖G (ξ - η)‖ := by
    positivity

  simpa [Real.norm_eq_abs, abs_of_nonneg hSumNonneg] using
    norm_h3WeightedRawProductKernelAt_le F G η ξ

/-- Canonical Fourier-`L²` package of the exact weighted kernel at fixed `η`. -/
noncomputable def h3WeightedRawProductKernelL2
    (F G : H3SpectralScalarState)
    (η : H3FourierPoint3) :
    H3FourierComplexL2 :=
  (h3WeightedRawProductKernelAt_memLp2 F G η).toLp
    (h3WeightedRawProductKernelAt F G η)

/-- The packaged weighted kernel has the expected representative a.e. -/
theorem h3WeightedRawProductKernelL2_ae
    (F G : H3SpectralScalarState)
    (η : H3FourierPoint3) :
    (h3WeightedRawProductKernelL2 F G η :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    h3WeightedRawProductKernelAt F G η := by
  exact
    MemLp.coeFn_toLp
      (h3WeightedRawProductKernelAt_memLp2 F G η)

end

end Euclidean
end Bridge
end PrimeTensor
