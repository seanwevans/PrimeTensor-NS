import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel

/-!
# Bilinearity of the genuine weighted H³ product convolution

The H³ algebra estimate has already packaged the exact weighted Fourier
convolution

    W(ξ) ∫ f̂(η) ĝ(ξ - η) dη

as `h3WeightedRawProductConvolutionL2`.

For the Picard subtraction identity we also need its algebra, not only its
norm.  This file proves additivity and subtractivity in both arguments.

There are two representative-level details:

* an `Lp` sum or difference agrees with the corresponding pointwise operation
  only almost everywhere;
* in the second convolution slot that a.e. equality is pulled back through
  `η ↦ ξ - η`.

The latter map is quasi-measure-preserving for Haar volume, exactly the
translation/reflection fact used by Mathlib's convolution API.  The existing
`h3RawProductKernel_integrable` theorem then justifies `integral_add` and
`integral_sub`.

No new analytic estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3WeightedConvolutionBilinear
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Deweighted representatives respect additive structure a.e. -/

/-- Deweighting an `Lp` sum agrees a.e. with the pointwise sum. -/
theorem h3SpectralScalarRawFourier_add_ae
    (F G : H3SpectralScalarState) :
    h3SpectralScalarRawFourier (F + G)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      h3SpectralScalarRawFourier F ξ +
        h3SpectralScalarRawFourier G ξ) := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_add F G
  ] with ξ hξ
  unfold h3SpectralScalarRawFourier
  rw [hξ]
  simp only [Pi.add_apply]
  ring

/-- Deweighting an `Lp` difference agrees a.e. with the pointwise difference. -/
theorem h3SpectralScalarRawFourier_sub_ae
    (F G : H3SpectralScalarState) :
    h3SpectralScalarRawFourier (F - G)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      h3SpectralScalarRawFourier F ξ -
        h3SpectralScalarRawFourier G ξ) := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub F G
  ] with ξ hξ
  unfold h3SpectralScalarRawFourier
  rw [hξ]
  simp only [Pi.sub_apply]
  ring

/-! ## Raw convolution bilinearity -/

/-- Raw convolution is additive in its first argument. -/
theorem h3RawProductConvolution_add_left
    (F G H : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3RawProductConvolution (F + G) H ξ
      =
    h3RawProductConvolution F H ξ +
      h3RawProductConvolution G H ξ := by
  have hRep :
      ∀ᵐ η : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3SpectralScalarRawFourier (F + G) η *
            h3SpectralScalarRawFourier H (ξ - η)
          =
        (h3SpectralScalarRawFourier F η +
            h3SpectralScalarRawFourier G η) *
          h3SpectralScalarRawFourier H (ξ - η) := by
    filter_upwards [
      h3SpectralScalarRawFourier_add_ae F G
    ] with η hη
    rw [hη]

  calc
    h3RawProductConvolution (F + G) H ξ
        =
      ∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier (F + G) η *
          h3SpectralScalarRawFourier H (ξ - η) := by
            rfl
    _ =
      ∫ η : H3FourierPoint3,
        (h3SpectralScalarRawFourier F η +
            h3SpectralScalarRawFourier G η) *
          h3SpectralScalarRawFourier H (ξ - η) :=
      integral_congr_ae hRep
    _ =
      ∫ η : H3FourierPoint3,
        (h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier H (ξ - η))
          +
        (h3SpectralScalarRawFourier G η *
            h3SpectralScalarRawFourier H (ξ - η)) := by
          apply integral_congr_ae
          filter_upwards with η
          ring
    _ =
      (∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier H (ξ - η))
        +
      (∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier G η *
          h3SpectralScalarRawFourier H (ξ - η)) := by
          rw [integral_add
            (h3RawProductKernel_integrable F H ξ)
            (h3RawProductKernel_integrable G H ξ)]
    _ =
      h3RawProductConvolution F H ξ +
        h3RawProductConvolution G H ξ := by
          rfl

/-- Raw convolution is subtractive in its first argument. -/
theorem h3RawProductConvolution_sub_left
    (F G H : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3RawProductConvolution (F - G) H ξ
      =
    h3RawProductConvolution F H ξ -
      h3RawProductConvolution G H ξ := by
  have hRep :
      ∀ᵐ η : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3SpectralScalarRawFourier (F - G) η *
            h3SpectralScalarRawFourier H (ξ - η)
          =
        (h3SpectralScalarRawFourier F η -
            h3SpectralScalarRawFourier G η) *
          h3SpectralScalarRawFourier H (ξ - η) := by
    filter_upwards [
      h3SpectralScalarRawFourier_sub_ae F G
    ] with η hη
    rw [hη]

  calc
    h3RawProductConvolution (F - G) H ξ
        =
      ∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier (F - G) η *
          h3SpectralScalarRawFourier H (ξ - η) := by
            rfl
    _ =
      ∫ η : H3FourierPoint3,
        (h3SpectralScalarRawFourier F η -
            h3SpectralScalarRawFourier G η) *
          h3SpectralScalarRawFourier H (ξ - η) :=
      integral_congr_ae hRep
    _ =
      ∫ η : H3FourierPoint3,
        (h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier H (ξ - η))
          -
        (h3SpectralScalarRawFourier G η *
            h3SpectralScalarRawFourier H (ξ - η)) := by
          apply integral_congr_ae
          filter_upwards with η
          ring
    _ =
      (∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier H (ξ - η))
        -
      (∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier G η *
          h3SpectralScalarRawFourier H (ξ - η)) := by
          rw [integral_sub
            (h3RawProductKernel_integrable F H ξ)
            (h3RawProductKernel_integrable G H ξ)]
    _ =
      h3RawProductConvolution F H ξ -
        h3RawProductConvolution G H ξ := by
          rfl

/-- Raw convolution is additive in its second argument. -/
theorem h3RawProductConvolution_add_right
    (F G H : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3RawProductConvolution F (G + H) ξ
      =
    h3RawProductConvolution F G ξ +
      h3RawProductConvolution F H ξ := by
  have hShiftComp :=
    (h3SpectralScalarRawFourier_add_ae G H).comp_tendsto
      (quasiMeasurePreserving_sub_left_of_right_invariant
        (volume : Measure H3FourierPoint3) ξ).tendsto_ae
  have hShift :
      ∀ᵐ η : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3SpectralScalarRawFourier (G + H) (ξ - η)
          =
        h3SpectralScalarRawFourier G (ξ - η) +
          h3SpectralScalarRawFourier H (ξ - η) := by
    filter_upwards [hShiftComp] with η hη
    simpa only [Function.comp_apply] using hη

  have hRep :
      ∀ᵐ η : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier (G + H) (ξ - η)
          =
        h3SpectralScalarRawFourier F η *
          (h3SpectralScalarRawFourier G (ξ - η) +
            h3SpectralScalarRawFourier H (ξ - η)) := by
    filter_upwards [hShift] with η hη
    rw [hη]

  calc
    h3RawProductConvolution F (G + H) ξ
        =
      ∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier (G + H) (ξ - η) := by
            rfl
    _ =
      ∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          (h3SpectralScalarRawFourier G (ξ - η) +
            h3SpectralScalarRawFourier H (ξ - η)) :=
      integral_congr_ae hRep
    _ =
      ∫ η : H3FourierPoint3,
        (h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η))
          +
        (h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier H (ξ - η)) := by
          apply integral_congr_ae
          filter_upwards with η
          ring
    _ =
      (∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η))
        +
      (∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier H (ξ - η)) := by
          rw [integral_add
            (h3RawProductKernel_integrable F G ξ)
            (h3RawProductKernel_integrable F H ξ)]
    _ =
      h3RawProductConvolution F G ξ +
        h3RawProductConvolution F H ξ := by
          rfl

/-- Raw convolution is subtractive in its second argument. -/
theorem h3RawProductConvolution_sub_right
    (F G H : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3RawProductConvolution F (G - H) ξ
      =
    h3RawProductConvolution F G ξ -
      h3RawProductConvolution F H ξ := by
  have hShiftComp :=
    (h3SpectralScalarRawFourier_sub_ae G H).comp_tendsto
      (quasiMeasurePreserving_sub_left_of_right_invariant
        (volume : Measure H3FourierPoint3) ξ).tendsto_ae
  have hShift :
      ∀ᵐ η : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3SpectralScalarRawFourier (G - H) (ξ - η)
          =
        h3SpectralScalarRawFourier G (ξ - η) -
          h3SpectralScalarRawFourier H (ξ - η) := by
    filter_upwards [hShiftComp] with η hη
    simpa only [Function.comp_apply] using hη

  have hRep :
      ∀ᵐ η : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier (G - H) (ξ - η)
          =
        h3SpectralScalarRawFourier F η *
          (h3SpectralScalarRawFourier G (ξ - η) -
            h3SpectralScalarRawFourier H (ξ - η)) := by
    filter_upwards [hShift] with η hη
    rw [hη]

  calc
    h3RawProductConvolution F (G - H) ξ
        =
      ∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier (G - H) (ξ - η) := by
            rfl
    _ =
      ∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          (h3SpectralScalarRawFourier G (ξ - η) -
            h3SpectralScalarRawFourier H (ξ - η)) :=
      integral_congr_ae hRep
    _ =
      ∫ η : H3FourierPoint3,
        (h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η))
          -
        (h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier H (ξ - η)) := by
          apply integral_congr_ae
          filter_upwards with η
          ring
    _ =
      (∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η))
        -
      (∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier H (ξ - η)) := by
          rw [integral_sub
            (h3RawProductKernel_integrable F G ξ)
            (h3RawProductKernel_integrable F H ξ)]
    _ =
      h3RawProductConvolution F G ξ -
        h3RawProductConvolution F H ξ := by
          rfl

/-! ## Exact weighted convolution bilinearity -/

theorem h3WeightedRawProductConvolution_add_left
    (F G H : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3WeightedRawProductConvolution (F + G) H ξ
      =
    h3WeightedRawProductConvolution F H ξ +
      h3WeightedRawProductConvolution G H ξ := by
  unfold h3WeightedRawProductConvolution
  rw [h3RawProductConvolution_add_left]
  ring

theorem h3WeightedRawProductConvolution_sub_left
    (F G H : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3WeightedRawProductConvolution (F - G) H ξ
      =
    h3WeightedRawProductConvolution F H ξ -
      h3WeightedRawProductConvolution G H ξ := by
  unfold h3WeightedRawProductConvolution
  rw [h3RawProductConvolution_sub_left]
  ring

theorem h3WeightedRawProductConvolution_add_right
    (F G H : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3WeightedRawProductConvolution F (G + H) ξ
      =
    h3WeightedRawProductConvolution F G ξ +
      h3WeightedRawProductConvolution F H ξ := by
  unfold h3WeightedRawProductConvolution
  rw [h3RawProductConvolution_add_right]
  ring

theorem h3WeightedRawProductConvolution_sub_right
    (F G H : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3WeightedRawProductConvolution F (G - H) ξ
      =
    h3WeightedRawProductConvolution F G ξ -
      h3WeightedRawProductConvolution F H ξ := by
  unfold h3WeightedRawProductConvolution
  rw [h3RawProductConvolution_sub_right]
  ring

/-! ## Bundled `L²` bilinearity -/

theorem h3WeightedRawProductConvolutionL2_add_left
    (F G H : H3SpectralScalarState) :
    h3WeightedRawProductConvolutionL2 (F + G) H
      =
    h3WeightedRawProductConvolutionL2 F H +
      h3WeightedRawProductConvolutionL2 G H := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3WeightedRawProductConvolutionL2_ae (F + G) H,
    h3WeightedRawProductConvolutionL2_ae F H,
    h3WeightedRawProductConvolutionL2_ae G H,
    MeasureTheory.Lp.coeFn_add
      (h3WeightedRawProductConvolutionL2 F H)
      (h3WeightedRawProductConvolutionL2 G H)
  ] with ξ hLeft hF hG hAdd
  rw [hLeft, hAdd]
  change
    h3WeightedRawProductConvolution (F + G) H ξ =
      (h3WeightedRawProductConvolutionL2 F H :
        H3FourierPoint3 → ℂ) ξ +
      (h3WeightedRawProductConvolutionL2 G H :
        H3FourierPoint3 → ℂ) ξ
  rw [hF, hG,
    h3WeightedRawProductConvolution_add_left]

theorem h3WeightedRawProductConvolutionL2_sub_left
    (F G H : H3SpectralScalarState) :
    h3WeightedRawProductConvolutionL2 (F - G) H
      =
    h3WeightedRawProductConvolutionL2 F H -
      h3WeightedRawProductConvolutionL2 G H := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3WeightedRawProductConvolutionL2_ae (F - G) H,
    h3WeightedRawProductConvolutionL2_ae F H,
    h3WeightedRawProductConvolutionL2_ae G H,
    MeasureTheory.Lp.coeFn_sub
      (h3WeightedRawProductConvolutionL2 F H)
      (h3WeightedRawProductConvolutionL2 G H)
  ] with ξ hLeft hF hG hSub
  rw [hLeft, hSub]
  change
    h3WeightedRawProductConvolution (F - G) H ξ =
      (h3WeightedRawProductConvolutionL2 F H :
        H3FourierPoint3 → ℂ) ξ -
      (h3WeightedRawProductConvolutionL2 G H :
        H3FourierPoint3 → ℂ) ξ
  rw [hF, hG,
    h3WeightedRawProductConvolution_sub_left]

theorem h3WeightedRawProductConvolutionL2_add_right
    (F G H : H3SpectralScalarState) :
    h3WeightedRawProductConvolutionL2 F (G + H)
      =
    h3WeightedRawProductConvolutionL2 F G +
      h3WeightedRawProductConvolutionL2 F H := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3WeightedRawProductConvolutionL2_ae F (G + H),
    h3WeightedRawProductConvolutionL2_ae F G,
    h3WeightedRawProductConvolutionL2_ae F H,
    MeasureTheory.Lp.coeFn_add
      (h3WeightedRawProductConvolutionL2 F G)
      (h3WeightedRawProductConvolutionL2 F H)
  ] with ξ hLeft hG hH hAdd
  rw [hLeft, hAdd]
  change
    h3WeightedRawProductConvolution F (G + H) ξ =
      (h3WeightedRawProductConvolutionL2 F G :
        H3FourierPoint3 → ℂ) ξ +
      (h3WeightedRawProductConvolutionL2 F H :
        H3FourierPoint3 → ℂ) ξ
  rw [hG, hH,
    h3WeightedRawProductConvolution_add_right]

theorem h3WeightedRawProductConvolutionL2_sub_right
    (F G H : H3SpectralScalarState) :
    h3WeightedRawProductConvolutionL2 F (G - H)
      =
    h3WeightedRawProductConvolutionL2 F G -
      h3WeightedRawProductConvolutionL2 F H := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3WeightedRawProductConvolutionL2_ae F (G - H),
    h3WeightedRawProductConvolutionL2_ae F G,
    h3WeightedRawProductConvolutionL2_ae F H,
    MeasureTheory.Lp.coeFn_sub
      (h3WeightedRawProductConvolutionL2 F G)
      (h3WeightedRawProductConvolutionL2 F H)
  ] with ξ hLeft hG hH hSub
  rw [hLeft, hSub]
  change
    h3WeightedRawProductConvolution F (G - H) ξ =
      (h3WeightedRawProductConvolutionL2 F G :
        H3FourierPoint3 → ℂ) ξ -
      (h3WeightedRawProductConvolutionL2 F H :
        H3FourierPoint3 → ℂ) ξ
  rw [hG, hH,
    h3WeightedRawProductConvolution_sub_right]

end

end Euclidean
end Bridge
end PrimeTensor
