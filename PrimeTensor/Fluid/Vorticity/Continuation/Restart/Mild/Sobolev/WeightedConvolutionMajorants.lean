import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.WeightedConvolutionDomination

/-!
# Measurable endpoint-Young majorants for the weighted H³ convolution

The weighted pointwise estimate is already closed.  Its right-hand side consists of two scalar
endpoint Young convolutions,

    A(F,G)(ξ) = ∫ η, ‖ĝ(η)‖ ‖F(ξ - η)‖,
    B(F,G)(ξ) = ∫ η, ‖f̂(η)‖ ‖G(ξ - η)‖.

Before proving their `L²` bounds, this file packages them as named functions and records the
measurability needed by `MemLp`.  Joint measurability is obtained from Mathlib's convolution
integrand theorem on the additive Haar carrier, followed by measurability of the inner Bochner
integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter ContinuousLinearMap
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3WeightedConvolutionMajorants
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- First endpoint-Young majorant, with raw `G` in the `L¹` slot. -/
noncomputable def h3FirstYoungMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier G η‖ * ‖F (ξ - η)‖

/-- Second endpoint-Young majorant, with raw `F` in the `L¹` slot. -/
noncomputable def h3SecondYoungMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F η‖ * ‖G (ξ - η)‖

/-- The complete scalar majorant appearing in the weighted product estimate. -/
noncomputable def h3WeightedYoungMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  8 * (h3FirstYoungMajorant F G ξ + h3SecondYoungMajorant F G ξ)

/-- The oriented first majorant integrand is integrable at every output frequency. -/
theorem h3FirstYoungMajorant_oriented_integrable
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    Integrable
      (fun η : H3FourierPoint3 =>
        ‖h3SpectralScalarRawFourier G η‖ * ‖F (ξ - η)‖)
      (volume : Measure H3FourierPoint3) := by
  rw [← memLp_one_iff_integrable]
  simpa only [mul_comm] using
    (h3SpectralScalarRawFourier_memLp2 G).norm.mul'
      (r := (1 : ENNReal))
      (h3SpectralScalarState_reflectedShift_memLp2 F ξ).norm

/-- The oriented second majorant integrand is integrable at every output frequency. -/
theorem h3SecondYoungMajorant_oriented_integrable
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    Integrable
      (fun η : H3FourierPoint3 =>
        ‖h3SpectralScalarRawFourier F η‖ * ‖G (ξ - η)‖)
      (volume : Measure H3FourierPoint3) := by
  exact h3SecondYoungMajorant_integrable F G ξ

/-- The first scalar majorant is a.e. strongly measurable in the output frequency. -/
theorem h3FirstYoungMajorant_aestronglyMeasurable
    (F G : H3SpectralScalarState) :
    AEStronglyMeasurable
      (h3FirstYoungMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hRaw :
      AEStronglyMeasurable
        (fun η : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G η‖)
        (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourier_memLp2 G).1.norm

  have hWeighted :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 => ‖F ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.aestronglyMeasurable F).norm

  have hJoint :
      AEStronglyMeasurable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G p.2‖ * ‖F (p.1 - p.2)‖)
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    simpa only [mul_apply'] using
      hRaw.convolution_integrand (mul ℝ ℝ) hWeighted

  exact hJoint.integral_prod_right'

/-- The second scalar majorant is a.e. strongly measurable in the output frequency. -/
theorem h3SecondYoungMajorant_aestronglyMeasurable
    (F G : H3SpectralScalarState) :
    AEStronglyMeasurable
      (h3SecondYoungMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hRaw :
      AEStronglyMeasurable
        (fun η : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourier_memLp2 F).1.norm

  have hWeighted :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 => ‖G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.aestronglyMeasurable G).norm

  have hJoint :
      AEStronglyMeasurable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F p.2‖ * ‖G (p.1 - p.2)‖)
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    simpa only [mul_apply'] using
      hRaw.convolution_integrand (mul ℝ ℝ) hWeighted

  exact hJoint.integral_prod_right'

/-- The complete weighted Young majorant is a.e. strongly measurable. -/
theorem h3WeightedYoungMajorant_aestronglyMeasurable
    (F G : H3SpectralScalarState) :
    AEStronglyMeasurable
      (h3WeightedYoungMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3WeightedYoungMajorant
  exact
    ((h3FirstYoungMajorant_aestronglyMeasurable F G).add
      (h3SecondYoungMajorant_aestronglyMeasurable F G)).const_mul 8

/-- Both endpoint-Young majorants are pointwise nonnegative. -/
theorem h3FirstYoungMajorant_nonneg
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    0 ≤ h3FirstYoungMajorant F G ξ := by
  unfold h3FirstYoungMajorant
  exact integral_nonneg fun η => mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem h3SecondYoungMajorant_nonneg
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    0 ≤ h3SecondYoungMajorant F G ξ := by
  unfold h3SecondYoungMajorant
  exact integral_nonneg fun η => mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The previously proved weighted convolution estimate in named-majorant form. -/
theorem norm_h3WeightedRawProductConvolution_le_majorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3WeightedRawProductConvolution F G ξ‖
      ≤ h3WeightedYoungMajorant F G ξ := by
  simpa [h3WeightedYoungMajorant, h3FirstYoungMajorant, h3SecondYoungMajorant] using
    norm_h3WeightedRawProductConvolution_le_youngMajorants F G ξ

end

end Euclidean
end Bridge
end PrimeTensor
