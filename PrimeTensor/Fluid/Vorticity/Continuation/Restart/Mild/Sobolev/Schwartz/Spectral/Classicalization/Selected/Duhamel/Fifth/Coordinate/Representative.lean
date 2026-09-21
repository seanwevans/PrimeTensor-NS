import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Fourth.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Raw.Fifth.Moment
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Classicalization: selected Duhamel fifth-coordinate reconstruction

The order-three old-history generator trace requires the genuine fifth spatial
Fréchet derivative of the literal selected Duhamel reconstruction.

Rather than expanding five coordinate symbols by hand, this file uses
Mathlib's order-generic multilinear Fourier multiplier and evaluates it on the
five canonical directions attached to `a,b,c,d,e`.

The named selected Duhamel raw amplitude now has an integrable fifth radial
moment.  Mathlib's inverse-Fourier differentiability theorem therefore
identifies the inverse Fourier transform of the evaluated order-five
multiplier with

    D⁵ Duhamel(t,x)[e_a,e_b,e_c,e_d,e_e].

No temporal differentiation and no new estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFifthCoordinateRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier amplitude for one ordered fifth spatial coordinate derivative
of the named selected Duhamel reconstruction. -/
noncomputable def h3SelectedDuhamelFifthCoordinateRawAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c d e : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  let m : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c),
      h3FourierAxisDirection (h3AxisOfFin3 d),
      h3FourierAxisDirection (h3AxisOfFin3 e)
    ]
  VectorFourier.fourierPowSMulRight
    (-(innerSL ℝ :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ))
    (h3SelectedDuhamelRawFourierAmplitude
      ν A t hν U₀ hA hU₀ ht i)
    ξ
    5
    m

/-- Every ordered fifth-coordinate selected-Duhamel raw amplitude is
integrable in the strict positive restart interval. -/
theorem h3SelectedDuhamelFifthCoordinateRawAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c d e : Fin 3) :
    Integrable
      (h3SelectedDuhamelFifthCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b c d e)
      (volume : Measure H3FourierPoint3) := by
  let f : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelRawFourierAmplitude
      ν A t hν U₀ hA hU₀ ht i

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c),
      h3FourierAxisDirection (h3AxisOfFin3 d),
      h3FourierAxisDirection (h3AxisOfFin3 e)
    ]

  have hAmpInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_integrable
        hν U₀ hA hU₀ ht i

  have hFive :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_fifthMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 5)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L hFive hAmpInt.aestronglyMeasurable

  have hEvalInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (VectorFourier.fourierPowSMulRight
            L f ξ 5) m)
        (volume : Measure H3FourierPoint3) :=
    ContinuousLinearMap.integrable_comp
      (ContinuousMultilinearMap.apply
        ℝ
        (fun _ : Fin 5 => H3FourierPoint3)
        ℂ
        m)
      hPowInt

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        (VectorFourier.fourierPowSMulRight
          (-(innerSL ℝ :
            H3FourierPoint3 →L[ℝ]
              H3FourierPoint3 →L[ℝ] ℝ))
          (h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i)
          ξ
          5)
          m)
      (volume : Measure H3FourierPoint3)

  simpa only [L, f, m] using hEvalInt

/-- One selected-Duhamel fifth-coordinate raw amplitude reconstructs exactly
the evaluated fifth Fréchet derivative of the named selected-Duhamel
inverse-Fourier representative. -/
theorem h3SelectedDuhamelFifthCoordinateRepresentative_eq_iteratedFDeriv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c d e : Fin 3)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelFifthCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b c d e)
        x
      =
    iteratedFDeriv ℝ 5
      (h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c),
        h3FourierAxisDirection (h3AxisOfFin3 d),
        h3FourierAxisDirection (h3AxisOfFin3 e)
      ] := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  let f : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelRawFourierAmplitude
      ν A t hν U₀ hA hU₀ ht i

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c),
      h3FourierAxisDirection (h3AxisOfFin3 d),
      h3FourierAxisDirection (h3AxisOfFin3 e)
    ]

  have hSelected0 :=
    h3SpectralScalarRawFourier_selectedDuhamel_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  have hSelected :
      h3SpectralScalarRawFourier D
        =ᵐ[(volume : Measure H3FourierPoint3)]
      f := by
    dsimp only [D, W, f]
    simpa only [W] using hSelected0

  have hAmpInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_integrable
        hν U₀ hA hU₀ ht i

  have hFirstD :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3SpectralScalarRawFourier D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourier_firstMoment_integrable D

  have hFirst :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hFirstD.congr ?_
    filter_upwards [hSelected] with ξ hξ
    rw [hξ]

  have hSecond :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hThird :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFourth :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFifth :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_fifthMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMom :
      ∀ (n : ℕ), n ≤ (5 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn5 : n ≤ 5 := by
      exact_mod_cast hn
    have hnCases :
        n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
      omega
    rcases hnCases with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [pow_zero, one_mul] using hAmpInt.norm
    · simpa only [pow_one] using hFirst
    · exact hSecond
    · exact hThird
    · exact hFourth
    · exact hFifth

  have hMeas :
      AEStronglyMeasurable
        f
        (volume : Measure H3FourierPoint3) :=
    hAmpInt.aestronglyMeasurable

  have hDeriv :=
    VectorFourier.iteratedFDeriv_fourierIntegral
      (L := L)
      (f := f)
      (μ := (volume : Measure H3FourierPoint3))
      hMom
      hMeas
      (n := 5)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 5)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 5 (by norm_num))
      hMeas

  rw [
    Real.fourierIntegral_continuousMultilinearMap_apply'
      hPowInt
  ] at hEval

  have hInner :
      ContinuousLinearMap.toLinearMap₁₂
          (-(innerSL ℝ :
            H3FourierPoint3 →L[ℝ]
              H3FourierPoint3 →L[ℝ] ℝ))
        =
      -(innerₗ H3FourierPoint3) := by
    ext v w
    simp only [
      ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      neg_apply,
      innerSL_apply_apply,
      LinearMap.neg_apply,
      innerₗ_apply_apply
    ]

  dsimp only [L] at hEval
  rw [hInner] at hEval

  unfold h3SelectedDuhamelFifthCoordinateRawAmplitude

  unfold h3SelectedDuhamelC1Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            (-(innerSL ℝ :
              H3FourierPoint3 →L[ℝ]
                H3FourierPoint3 →L[ℝ] ℝ))
            f ξ 5 m)
        x
      =
    iteratedFDeriv ℝ 5
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x
      m

  exact hEval.symm

/-- The same fifth-coordinate reconstruction is the genuine fifth Fréchet
derivative of the literal selected classical Duhamel integral. -/
theorem h3SelectedDuhamelFifthCoordinateRepresentative_eq_C3Duhamel_iteratedFDeriv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c d e : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelFifthCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b c d e)
        x
      =
    iteratedFDeriv ℝ 5
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c),
        h3FourierAxisDirection (h3AxisOfFin3 d),
        h3FourierAxisDirection (h3AxisOfFin3 e)
      ] := by
  dsimp only

  have hFifth :=
    h3SelectedDuhamelFifthCoordinateRepresentative_eq_iteratedFDeriv
      hν U₀ hA hU₀ ht htR i a b c d e x

  have hFull :=
    h3SelectedDuhamelC1Representative_eq_C3Duhamel
      hν U₀ hA hU₀ ht htR i

  dsimp only at hFull
  rw [hFull] at hFifth
  exact hFifth

end

end Euclidean
end Bridge
end PrimeTensor
