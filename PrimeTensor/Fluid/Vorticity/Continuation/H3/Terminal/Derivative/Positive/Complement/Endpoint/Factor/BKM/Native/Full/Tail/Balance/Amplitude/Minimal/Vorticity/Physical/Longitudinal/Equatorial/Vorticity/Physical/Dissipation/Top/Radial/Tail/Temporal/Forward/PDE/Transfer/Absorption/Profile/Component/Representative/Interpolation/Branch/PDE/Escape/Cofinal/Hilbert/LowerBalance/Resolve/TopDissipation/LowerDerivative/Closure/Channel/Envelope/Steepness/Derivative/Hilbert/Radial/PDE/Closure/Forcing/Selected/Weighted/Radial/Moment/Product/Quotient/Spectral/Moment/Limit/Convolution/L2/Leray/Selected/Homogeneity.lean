import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.Bilinear

/-!
# Real scalar homogeneity of the raw finite Leray form

The forcing quotient uses the real scalar `h⁻¹` applied to a spectral
difference.  Subtractivity of the raw convolution and Leray form is already
available, but scalar homogeneity has not previously been packaged.

This file proves the missing real-linear algebra:

* deweighting commutes a.e. with real scalar multiplication;
* raw product convolution is homogeneous in either slot;
* finite outer-product divergence is homogeneous in either slot;
* the complete finite Leray-divergence forcing is homogeneous in either slot.

No analytic estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3RawFinLerayRealHomogeneity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1600000

/-! ## Deweighting -/

/--
Deweighting a real scalar multiple agrees almost everywhere with multiplying
the raw Fourier representative by the corresponding complex scalar.
-/
theorem h3SpectralScalarRawFourier_smul_real_ae
    (c : ℝ)
    (F : H3SpectralScalarState) :
    h3SpectralScalarRawFourier (c • F)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (c : ℂ) * h3SpectralScalarRawFourier F ξ) := by

  have hSmul :=
    MeasureTheory.Lp.coeFn_smul c F

  filter_upwards [hSmul] with ξ hξ

  unfold h3SpectralScalarRawFourier

  rw [hξ]

  simp only [
    Pi.smul_apply,
    Complex.real_smul
  ]

  ring

/-! ## Raw convolution -/

/--
Raw product convolution is homogeneous over real scalars in its first slot.
-/
theorem h3RawProductConvolution_smul_left_real
    (c : ℝ)
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3RawProductConvolution (c • F) G ξ
      =
    (c : ℂ) * h3RawProductConvolution F G ξ := by

  have hRep :=
    h3SpectralScalarRawFourier_smul_real_ae c F

  calc
    h3RawProductConvolution (c • F) G ξ
        =
      ∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier (c • F) η *
          h3SpectralScalarRawFourier G (ξ - η) := by
            rfl
    _ =
      ∫ η : H3FourierPoint3,
        ((c : ℂ) * h3SpectralScalarRawFourier F η) *
          h3SpectralScalarRawFourier G (ξ - η) := by
            apply integral_congr_ae
            filter_upwards [hRep] with η hη
            rw [hη]
    _ =
      ∫ η : H3FourierPoint3,
        (c : ℂ) *
          (
            h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)
          ) := by
            apply integral_congr_ae
            filter_upwards with η
            ring
    _ =
      (c : ℂ) *
        ∫ η : H3FourierPoint3,
          h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η) := by
              rw [integral_const_mul]
    _ =
      (c : ℂ) *
        h3RawProductConvolution F G ξ := by
          rfl

/--
Raw product convolution is homogeneous over real scalars in its second slot.
-/
theorem h3RawProductConvolution_smul_right_real
    (c : ℝ)
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3RawProductConvolution F (c • G) ξ
      =
    (c : ℂ) * h3RawProductConvolution F G ξ := by

  have hShiftComp :=
    (h3SpectralScalarRawFourier_smul_real_ae c G).comp_tendsto
      (quasiMeasurePreserving_sub_left_of_right_invariant
        (volume : Measure H3FourierPoint3) ξ).tendsto_ae

  have hShift :
      ∀ᵐ η : H3FourierPoint3
        ∂(volume : Measure H3FourierPoint3),
        h3SpectralScalarRawFourier (c • G) (ξ - η)
          =
        (c : ℂ) *
          h3SpectralScalarRawFourier G (ξ - η) := by
    filter_upwards [hShiftComp] with η hη
    simpa only [Function.comp_apply] using hη

  calc
    h3RawProductConvolution F (c • G) ξ
        =
      ∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier (c • G) (ξ - η) := by
            rfl
    _ =
      ∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          ((c : ℂ) *
            h3SpectralScalarRawFourier G (ξ - η)) := by
            apply integral_congr_ae
            filter_upwards [hShift] with η hη
            rw [hη]
    _ =
      ∫ η : H3FourierPoint3,
        (c : ℂ) *
          (
            h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)
          ) := by
            apply integral_congr_ae
            filter_upwards with η
            ring
    _ =
      (c : ℂ) *
        ∫ η : H3FourierPoint3,
          h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η) := by
              rw [integral_const_mul]
    _ =
      (c : ℂ) *
        h3RawProductConvolution F G ξ := by
          rfl

/-! ## Finite divergence -/

/--
Finite outer-product divergence is homogeneous over real scalars in its first
vector slot.
-/
theorem h3RawFinOuterProductDivergence_smul_left_real
    (c : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinOuterProductDivergence (c • U) V i ξ
      =
    (c : ℂ) *
      h3RawFinOuterProductDivergence U V i ξ := by

  unfold h3RawFinOuterProductDivergence

  simp_rw [
    Pi.smul_apply,
    h3RawProductConvolution_smul_left_real
  ]

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro j hj

  ring

/--
Finite outer-product divergence is homogeneous over real scalars in its second
vector slot.
-/
theorem h3RawFinOuterProductDivergence_smul_right_real
    (c : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinOuterProductDivergence U (c • V) i ξ
      =
    (c : ℂ) *
      h3RawFinOuterProductDivergence U V i ξ := by

  unfold h3RawFinOuterProductDivergence

  simp_rw [
    Pi.smul_apply,
    h3RawProductConvolution_smul_right_real
  ]

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro j hj

  ring

/-! ## Complete finite Leray forcing -/

/--
The complete raw finite Leray-divergence forcing is homogeneous over real
scalars in its first vector slot.
-/
theorem h3RawFinLerayOuterProductDivergence_smul_left_real
    (c : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergence (c • U) V i ξ
      =
    (c : ℂ) *
      h3RawFinLerayOuterProductDivergence U V i ξ := by

  unfold h3RawFinLerayOuterProductDivergence

  simp_rw [
    h3RawFinOuterProductDivergence_smul_left_real
  ]

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro k hk

  ring

/--
The complete raw finite Leray-divergence forcing is homogeneous over real
scalars in its second vector slot.
-/
theorem h3RawFinLerayOuterProductDivergence_smul_right_real
    (c : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergence U (c • V) i ξ
      =
    (c : ℂ) *
      h3RawFinLerayOuterProductDivergence U V i ξ := by

  unfold h3RawFinLerayOuterProductDivergence

  simp_rw [
    h3RawFinOuterProductDivergence_smul_right_real
  ]

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro k hk

  ring

end

end Euclidean
end Bridge
end PrimeTensor
