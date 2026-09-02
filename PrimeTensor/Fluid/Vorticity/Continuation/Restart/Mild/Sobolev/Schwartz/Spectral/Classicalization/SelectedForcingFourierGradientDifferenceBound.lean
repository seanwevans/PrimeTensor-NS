import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedForcingFirstDifferenceContinuity
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Classicalization: Fourier-gradient difference bound for forcing amplitudes

The selected nonlinear forcing difference is now known to converge to zero in
the first weighted raw Fourier `L¹` topology.

This file records the generic analytic bridge from that topology to the
spatial Fréchet derivative of the ordinary Fourier reconstruction.

For integrable amplitudes `f` and `g` carrying one integrable raw Fourier
moment,

    ‖D 𝓕 f(x) - D 𝓕 g(x)‖
      ≤ C_Fourier ∫ ‖ξ‖ ‖f(ξ)-g(ξ)‖ dξ,

uniformly in `x`.

The proof is exactly Mathlib's Fourier differentiation formula followed by the
uniform `L¹` bound for the Fourier integral and the pointwise norm estimate for
`fourierSMulRight`.

This is the final generic Fourier-side estimate needed before transporting the
selected forcing gradient through inverse Fourier, `Point3`, and real-part
reconstruction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingFourierGradientDifferenceBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The fixed finite-dimensional Fourier differentiation constant used in the
first-gradient estimate. -/
noncomputable def h3FourierFirstDerivativeL1Coefficient : ℝ :=
  2 * Real.pi * ‖(innerSL ℝ :
    H3FourierPoint3 →L[ℝ] H3FourierPoint3 →L[ℝ] ℝ)‖

theorem h3FourierFirstDerivativeL1Coefficient_nonneg :
    0 ≤ h3FourierFirstDerivativeL1Coefficient := by
  unfold h3FourierFirstDerivativeL1Coefficient
  positivity

/-- The Fréchet derivative of the ordinary Fourier transform is Lipschitz with
respect to the first weighted raw `L¹` mass. -/
theorem norm_fderiv_fourier_sub_le_firstMass
    (f g : H3FourierPoint3 → ℂ)
    (hf0 :
      Integrable f
        (volume : Measure H3FourierPoint3))
    (hg0 :
      Integrable g
        (volume : Measure H3FourierPoint3))
    (hf1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3))
    (hg1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖g ξ‖)
        (volume : Measure H3FourierPoint3))
    (hfg1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖f ξ - g ξ‖)
        (volume : Measure H3FourierPoint3))
    (x : H3FourierPoint3) :
    ‖fderiv ℝ (FourierTransform.fourier f) x -
        fderiv ℝ (FourierTransform.fourier g) x‖
      ≤
    h3FourierFirstDerivativeL1Coefficient *
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖f ξ - g ξ‖ := by
  let h : H3FourierPoint3 → ℂ :=
    fun ξ => f ξ - g ξ

  have hh0 :
      Integrable h
        (volume : Measure H3FourierPoint3) := by
    dsimp only [h]
    exact hf0.sub hg0

  have hh1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [h] using hfg1

  have hfDiff :
      Differentiable ℝ
        (FourierTransform.fourier f) :=
    Real.differentiable_fourier hf0 hf1

  have hgDiff :
      Differentiable ℝ
        (FourierTransform.fourier g) :=
    Real.differentiable_fourier hg0 hg1

  have hhDiff :
      Differentiable ℝ
        (FourierTransform.fourier h) :=
    Real.differentiable_fourier hh0 hh1

  have hFourierSub :
      FourierTransform.fourier h
        =
      FourierTransform.fourier f -
        FourierTransform.fourier g := by
    ext x

    have hfi :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            Real.fourierChar (-inner ℝ ξ x) • f ξ)
          (volume : Measure H3FourierPoint3) :=
      (Real.fourierIntegral_convergent_iff x).2 hf0

    have hgi :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            Real.fourierChar (-inner ℝ ξ x) • g ξ)
          (volume : Measure H3FourierPoint3) :=
      (Real.fourierIntegral_convergent_iff x).2 hg0

    dsimp only [h]

    change
      FourierTransform.fourier
          (fun ξ : H3FourierPoint3 => f ξ - g ξ) x
        =
      FourierTransform.fourier f x -
        FourierTransform.fourier g x

    rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]

    change
      (∫ ξ : H3FourierPoint3,
        Real.fourierChar (-inner ℝ ξ x) •
          (f ξ - g ξ))
        =
      (∫ ξ : H3FourierPoint3,
        Real.fourierChar (-inner ℝ ξ x) • f ξ)
        -
      ∫ ξ : H3FourierPoint3,
        Real.fourierChar (-inner ℝ ξ x) • g ξ

    rw [← integral_sub hfi hgi]

    apply integral_congr_ae
    filter_upwards with ξ
    rw [smul_sub]

  have hFDerivSub :
      fderiv ℝ (FourierTransform.fourier h) x
        =
      fderiv ℝ (FourierTransform.fourier f) x -
        fderiv ℝ (FourierTransform.fourier g) x := by
    rw [hFourierSub]
    exact
      fderiv_sub
        (hfDiff.differentiableAt)
        (hgDiff.differentiableAt)

  rw [← hFDerivSub]

  have hFormula :
      fderiv ℝ (FourierTransform.fourier h) x
        =
      FourierTransform.fourier
        (VectorFourier.fourierSMulRight
          (innerSL ℝ) h) x := by
    have hAll :=
      Real.fderiv_fourier hh0 hh1
    exact congrFun hAll x

  rw [hFormula]

  have hFourierBound :=
    VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar
      (volume : Measure H3FourierPoint3)
      (innerₗ H3FourierPoint3)
      (VectorFourier.fourierSMulRight
        (innerSL ℝ) h)
      x

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFirstDerivativeL1Coefficient *
            (‖ξ‖ * ‖h ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hh1.const_mul
      h3FourierFirstDerivativeL1Coefficient

  have hSMulMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖VectorFourier.fourierSMulRight
            (innerSL ℝ) h ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      (hh0.aestronglyMeasurable.fourierSMulRight).norm

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierSMulRight
            (innerSL ℝ) h ξ‖
          ≤
        h3FourierFirstDerivativeL1Coefficient *
          (‖ξ‖ * ‖h ξ‖) := by
    intro ξ
    have hBase :=
      VectorFourier.norm_fourierSMulRight_le
        (innerSL ℝ)
        h
        ξ
    unfold h3FourierFirstDerivativeL1Coefficient
    simpa only [mul_assoc] using hBase

  have hSMul :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖VectorFourier.fourierSMulRight
            (innerSL ℝ) h ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hSMulMeas ?_
    filter_upwards with ξ
    have hLeft0 :
        0 ≤
          ‖VectorFourier.fourierSMulRight
            (innerSL ℝ) h ξ‖ := by
      positivity
    have hRight0 :
        0 ≤
          h3FourierFirstDerivativeL1Coefficient *
            (‖ξ‖ * ‖h ξ‖) := by
      exact
        mul_nonneg
          h3FourierFirstDerivativeL1Coefficient_nonneg
          (mul_nonneg (norm_nonneg ξ) (norm_nonneg (h ξ)))
    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hPoint ξ

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierSMulRight
          (innerSL ℝ) h ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3FourierFirstDerivativeL1Coefficient *
          (‖ξ‖ * ‖h ξ‖) := by
    exact
      integral_mono_ae
        hSMul
        hMajor
        (Filter.Eventually.of_forall hPoint)

  calc
    ‖FourierTransform.fourier
        (VectorFourier.fourierSMulRight
          (innerSL ℝ) h) x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierSMulRight
          (innerSL ℝ) h ξ‖ :=
      hFourierBound
    _ ≤
      ∫ ξ : H3FourierPoint3,
        h3FourierFirstDerivativeL1Coefficient *
          (‖ξ‖ * ‖h ξ‖) :=
      hIntegral
    _ =
      h3FourierFirstDerivativeL1Coefficient *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ * ‖h ξ‖ := by
      rw [integral_const_mul]
    _ =
      h3FourierFirstDerivativeL1Coefficient *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ * ‖f ξ - g ξ‖ := by
      rfl

end

end Euclidean
end Bridge
end PrimeTensor
