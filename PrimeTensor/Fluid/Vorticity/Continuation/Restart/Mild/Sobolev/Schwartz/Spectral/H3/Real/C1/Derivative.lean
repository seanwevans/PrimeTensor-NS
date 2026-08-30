import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fourier.Derivative.AE
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Coordinate derivatives of the arbitrary-H³ inverse-Fourier representative

`H3.Real.C1.Bridge` constructs, for every weighted H³ scalar spectral state
`G`, the classical representative

    x ↦ 𝓕⁻(W₃⁻¹ G)(x).

The bridge proves that this representative is `C¹`, but until now it did not
record the exact value of its coordinate derivative.

This file closes that formula.

For the raw Fourier field

    f(ξ) = W₃(ξ)⁻¹ G(ξ),

Mathlib gives

    D(𝓕 f)(y)[v]
      = 𝓕(ξ ↦ -2π i <ξ,v> f(ξ))(y).

Since inverse Fourier is `𝓕 f (-x)`, composition with `x ↦ -x` contributes one
more minus sign.  In the intrinsic coordinate direction corresponding to
`i : Fin 3`, the result is therefore exactly

    D_i (𝓕⁻ f)(x)
      = 𝓕⁻(ξ ↦ d_i(ξ) f(ξ))(x),

where `d_i(ξ) = 2π i ξ_i` is PrimeTensor's already-verified derivative
symbol.

This is the calculus identity needed to turn raw Fourier incompressibility
into physical-space incompressibility of the selected real velocity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3RealC1InverseFourierDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One raw coordinate Fourier derivative of an arbitrary H³ scalar state. -/
noncomputable def h3SpectralScalarRawFourierCoordinateDerivative
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    H3FourierPoint3 → ℂ :=
  fun ξ =>
    h3FourierDerivativeSymbol i ξ *
      h3SpectralScalarRawFourier G ξ

/-- The raw coordinate derivative multiplier is integrable.  This is the
first-moment content already proved from the exact H³ weight. -/
theorem h3SpectralScalarRawFourierCoordinateDerivative_integrable
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    Integrable
      (h3SpectralScalarRawFourierCoordinateDerivative G i)
      (volume : Measure H3FourierPoint3) := by
  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourier_firstMoment_integrable G

  have hDom :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul (2 * Real.pi)

  apply hDom.mono'
  · exact
      (h3FourierDerivativeSymbol_continuous i).aestronglyMeasurable.mul
        (MeasureTheory.memLp_one_iff_integrable.mp
          (h3SpectralScalarRawFourier_memLp1 G)).aestronglyMeasurable
  · filter_upwards with ξ

    unfold h3SpectralScalarRawFourierCoordinateDerivative

    calc
      ‖h3FourierDerivativeSymbol i ξ *
          h3SpectralScalarRawFourier G ξ‖
          =
        ‖h3FourierDerivativeSymbol i ξ‖ *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
            rw [norm_mul]
      _ ≤
        h3FourierGradientMagnitude ξ *
          ‖h3SpectralScalarRawFourier G ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_h3FourierDerivativeSymbol_le_gradientMagnitude i ξ)
          (norm_nonneg _)
      _ =
        (2 * Real.pi) *
          (‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖) := by
            unfold h3FourierGradientMagnitude
            ring

/-- The `fourierSMulRight` field occurring in Mathlib's Fréchet derivative
formula is integrable under the H³ first-moment estimate. -/
theorem h3SpectralScalarRawFourier_fourierSMulRight_integrable
    (G : H3SpectralScalarState) :
    Integrable
      (VectorFourier.fourierSMulRight
        (innerSL ℝ)
        (h3SpectralScalarRawFourier G))
      (volume : Measure H3FourierPoint3) := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier G

  have hf :
      Integrable f (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [f] using
      h3SpectralScalarRawFourier_firstMoment_integrable G

  have hDom :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi * ‖innerSL (E := H3FourierPoint3) ℝ‖) *
            (‖ξ‖ * ‖f ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul
      (2 * Real.pi * ‖innerSL (E := H3FourierPoint3) ℝ‖)

  apply hDom.mono'
  · exact
      hf.aestronglyMeasurable.fourierSMulRight
  · filter_upwards with ξ

    calc
      ‖VectorFourier.fourierSMulRight
          (innerSL ℝ) f ξ‖
          ≤
        2 * Real.pi *
          ‖innerSL (E := H3FourierPoint3) ℝ‖ *
          ‖ξ‖ * ‖f ξ‖ :=
        VectorFourier.norm_fourierSMulRight_le
          (innerSL ℝ) f ξ
      _ =
        (2 * Real.pi *
          ‖innerSL (E := H3FourierPoint3) ℝ‖) *
          (‖ξ‖ * ‖f ξ‖) := by
            ring

/-- Coordinate line derivative of the classical complex inverse-Fourier
representative of an arbitrary H³ state.

This is the exact inverse-Fourier counterpart of the forward multiplier
identity used by the H³ encoder. -/
theorem h3SpectralScalarC1Representative_hasLineDerivAt_fin
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    HasLineDerivAt ℝ
      (h3SpectralScalarC1Representative G)
      (FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative G i)
        x)
      x
      (h3FourierAxisDirection (h3AxisOfFin3 i)) := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier G

  let v : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 i)

  have hf :
      Integrable f (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [f] using
      h3SpectralScalarRawFourier_firstMoment_integrable G

  have hFourier :
      HasFDerivAt
        (FourierTransform.fourier f)
        (FourierTransform.fourier
          (VectorFourier.fourierSMulRight
            (innerSL ℝ) f)
          (-x))
        (-x) :=
    Real.hasFDerivAt_fourier hf hMoment (-x)

  have hComp :=
    hFourier.comp
      x
      ((hasFDerivAt_id x).neg)

  have hLine :=
    hComp.hasLineDerivAt v

  have hSMulInt :
      Integrable
        (VectorFourier.fourierSMulRight
          (innerSL ℝ) f)
        (volume : Measure H3FourierPoint3) := by
    simpa only [f] using
      h3SpectralScalarRawFourier_fourierSMulRight_integrable G

  have hDerivativeValue :
      ((FourierTransform.fourier
          (VectorFourier.fourierSMulRight
            (innerSL ℝ) f)
          (-x)).comp
        (-ContinuousLinearMap.id ℝ H3FourierPoint3))
        v
        =
      FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative G i)
        x := by
    rw [ContinuousLinearMap.comp_apply]
    simp only [
      neg_apply,
      ContinuousLinearMap.id_apply
    ]

    rw [Real.fourier_continuousLinearMap_apply hSMulInt]
    rw [Real.fourierInv_eq_fourier_neg]

    apply Real.fourier_congr_ae
    filter_upwards with ξ

    unfold h3SpectralScalarRawFourierCoordinateDerivative
    rw [h3FourierDerivativeSymbol_eq_inner]

    simp only [
      VectorFourier.fourierSMulRight_apply,
      v,
      smul_eq_mul
    ]

    rw [map_neg, innerSL_apply_apply]
    dsimp [f]
    push_cast
    ring

  rw [hDerivativeValue] at hLine

  have hRepresentativeEq :
      h3SpectralScalarC1Representative G
        =
      (FourierTransform.fourier f ∘ Neg.neg) := by
    funext y
    unfold h3SpectralScalarC1Representative
    change
      FourierTransformInv.fourierInv
          (h3SpectralScalarRawFourier G) y
        =
      FourierTransform.fourier f (-y)
    simpa only [f] using
      Real.fourierInv_eq_fourier_neg
        (h3SpectralScalarRawFourier G) y

  rw [hRepresentativeEq]
  simpa only [f, v] using hLine

end
end Euclidean
end Bridge
end PrimeTensor
