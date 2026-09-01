import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.HistoryQuotient

/-!
# Selected Duhamel old-history physical quotient

`HistoryQuotient` closed the right difference quotient after inverse Fourier
reconstruction.  Its quotient representative was intentionally defined by
first taking the raw Fourier quotient and only then applying inverse Fourier.

This file proves the remaining linearity bridge:

    F⁻¹[h⁻¹ (H_h - H_0)]
      =
    h⁻¹ (F⁻¹[H_h] - F⁻¹[H_0]).

For nonnegative elapsed heat time both raw heat amplitudes are Fourier `L¹`,
so ordinary inverse Fourier additivity applies to the subtraction.  Constant
scalar multiplication is linear without any additional integrability
hypothesis.

The zero-time old-history heat representative is already exactly the
canonical selected Duhamel pointwise representative.  Hence the Fourier-level
right quotient theorem immediately becomes the literal physical difference
quotient limit

    h⁻¹ • (oldHeat(h,x) - D(t,x))
      ⟶ generator(t,x)

as `h ↓ 0`.

This closes the old-history contribution in the exact pointwise form needed
for the diagonal Duhamel derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3DuhamelHistoryRepresentativeQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Inverse Fourier reconstruction commutes with the old-history normalized
difference for every nonnegative elapsed heat time. -/
theorem h3SelectedDuhamelHistoryHeatQuotientRepresentative_eq_inv_smul_sub
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 ≤ h)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3SelectedDuhamelHistoryHeatQuotientRepresentative
        ν A t h hν U₀ hA hU₀ ht i x
      =
    h⁻¹ •
      (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i x
        -
      h3SelectedDuhamelHistoryHeatRepresentative
          ν A t 0 hν U₀ hA hU₀ ht i x) := by
  let Hh : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelHistoryHeatRawAmplitude
      ν A t h hν U₀ hA hU₀ ht i

  let H0 : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelHistoryHeatRawAmplitude
      ν A t 0 hν U₀ hA hU₀ ht i

  have hHh :
      Integrable Hh (volume : Measure H3FourierPoint3) := by
    dsimp only [Hh]
    exact
      h3SelectedDuhamelHistoryHeatRawAmplitude_integrable_of_nonneg
        hν U₀ hA hU₀ ht hh i

  have hH0 :
      Integrable H0 (volume : Measure H3FourierPoint3) := by
    dsimp only [H0]
    exact
      h3SelectedDuhamelHistoryHeatRawAmplitude_integrable_of_nonneg
        hν U₀ hA hU₀ ht (le_refl (0 : ℝ)) i

  have hInnerNegContinuous :
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          -inner ℝ p.1 p.2)
    exact
      (continuous_inner
        (𝕜 := ℝ)
        (E := H3FourierPoint3)).neg

  have hInvNeg :
      FourierTransformInv.fourierInv (-H0) x
        =
      -FourierTransformInv.fourierInv H0 x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (-H0)
          x
        =
      -VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          H0
          x

    have hSmul :=
      congrFun
        (VectorFourier.fourierIntegral_const_smul
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          H0
          (-1 : ℂ))
        x

    simpa using hSmul

  have hInvAdd :
      FourierTransformInv.fourierInv (Hh + (-H0)) x
        =
      FourierTransformInv.fourierInv Hh x
        +
      FourierTransformInv.fourierInv (-H0) x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (Hh + (-H0))
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          Hh
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (-H0)
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          hHh
          hH0.neg)
        x

  have hInvSub :
      FourierTransformInv.fourierInv (Hh - H0) x
        =
      FourierTransformInv.fourierInv Hh x
        -
      FourierTransformInv.fourierInv H0 x := by
    rw [sub_eq_add_neg, hInvAdd, hInvNeg]
    rfl

  have hRawEq :
      h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i
        =
      (((h⁻¹ : ℝ) : ℂ) • (Hh - H0)) := by
    funext ξ
    unfold h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
    dsimp only [Hh, H0, Pi.sub_apply, Pi.smul_apply]
    simp only [smul_eq_mul]
    rfl

  have hInvSmul :
      FourierTransformInv.fourierInv
          ((((h⁻¹ : ℝ) : ℂ) • (Hh - H0))) x
        =
      (((h⁻¹ : ℝ) : ℂ) •
        FourierTransformInv.fourierInv (Hh - H0)) x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (((h⁻¹ : ℝ) : ℂ) • (Hh - H0))
          x
        =
      ((((h⁻¹ : ℝ) : ℂ) •
        VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (Hh - H0)) x)

    exact
      congrFun
        (VectorFourier.fourierIntegral_const_smul
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (Hh - H0)
          (((h⁻¹ : ℝ) : ℂ)))
        x

  unfold h3SelectedDuhamelHistoryHeatQuotientRepresentative
  rw [hRawEq, hInvSmul]
  simp only [Pi.smul_apply]
  rw [hInvSub]

  unfold h3SelectedDuhamelHistoryHeatRepresentative
  dsimp only [Hh, H0]
  exact
    Complex.coe_smul
      h⁻¹
      (FourierTransformInv.fourierInv
          (h3SelectedDuhamelHistoryHeatRawAmplitude
            ν A t h hν U₀ hA hU₀ ht i)
          x
        -
      FourierTransformInv.fourierInv
          (h3SelectedDuhamelHistoryHeatRawAmplitude
            ν A t 0 hν U₀ hA hU₀ ht i)
          x)

/-- Literal physical old-history difference quotient, based at the zero-time
old-history representative, converges from the right to the physical
old-history heat generator. -/
theorem tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeatRepresentative_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (h3SelectedDuhamelHistoryHeatRepresentative
              ν A t h hν U₀ hA hU₀ ht i x
            -
          h3SelectedDuhamelHistoryHeatRepresentative
              ν A t 0 hν U₀ hA hU₀ ht i x))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatTimeGeneratorRepresentative
          ν A t hν U₀ hA hU₀ ht i x)) := by
  have hQ :=
    tendsto_h3SelectedDuhamelHistoryHeatQuotientRepresentative_zero_right
      hν U₀ hA hU₀ ht htR i x

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          (h3SelectedDuhamelHistoryHeatRepresentative
              ν A t h hν U₀ hA hU₀ ht i x
            -
          h3SelectedDuhamelHistoryHeatRepresentative
              ν A t 0 hν U₀ hA hU₀ ht i x))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatQuotientRepresentative
          ν A t h hν U₀ hA hU₀ ht i x) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact
      (h3SelectedDuhamelHistoryHeatQuotientRepresentative_eq_inv_smul_sub
        hν U₀ hA hU₀ ht hh.le i x).symm

  exact Tendsto.congr' hEq.symm hQ

/-- The old-history quotient based at the canonical selected Duhamel
pointwise representative has the same right limit. -/
theorem tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeatRepresentative_C1_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (h3SelectedDuhamelHistoryHeatRepresentative
              ν A t h hν U₀ hA hU₀ ht i x
            -
          h3SelectedDuhamelC1Representative
              ν A t hν U₀ hA hU₀ ht i x))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatTimeGeneratorRepresentative
          ν A t hν U₀ hA hU₀ ht i x)) := by
  have hBase :=
    h3SelectedDuhamelHistoryHeatRepresentative_zero_eq_C1Representative
      hν U₀ hA hU₀ ht i

  have hQ :=
    tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeatRepresentative_zero_right
      hν U₀ hA hU₀ ht htR i x

  simpa only [congrFun hBase x] using hQ

end

end Euclidean
end Bridge
end PrimeTensor
