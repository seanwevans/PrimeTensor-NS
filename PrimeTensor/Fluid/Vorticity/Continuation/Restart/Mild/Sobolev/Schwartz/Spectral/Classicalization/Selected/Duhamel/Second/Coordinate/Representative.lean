import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.HistoryGenerator
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Full.Pointwise
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Derivative

/-!
# Classicalization: selected Duhamel second-coordinate reconstruction

The order-two old-history quotient has now been closed at the raw Fourier
level.  Its literal representative bridge needs the base selected Duhamel
Hessian coordinate written as the inverse Fourier transform of

    d_a(ξ) d_b(ξ) A_t(ξ),

where `A_t` is the named selected Duhamel raw amplitude.

This file supplies that missing quadratic counterpart of the already-compiled
selected Duhamel third-coordinate reconstruction.

The required moments through order two are already available:

* order 0: the selected raw `L¹` reconstruction theorem;
* order 1: the generic H³ first moment, transported across the selected raw
  a.e. representative bridge;
* order 2: the selected Duhamel second-moment theorem.

No temporal differentiation or new estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondCoordinateRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier amplitude for an ordered pair of canonical coordinate
derivatives of the named selected Duhamel reconstruction. -/
noncomputable def h3SelectedDuhamelSecondCoordinateRawAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    (h3FourierDerivativeSymbol b ξ *
      h3SelectedDuhamelRawFourierAmplitude
        ν A t hν U₀ hA hU₀ ht i ξ)

/-- The ordered pair of project derivative symbols is exactly Mathlib's
order-two inverse-Fourier multiplier on the corresponding canonical
directions. -/
theorem h3SelectedDuhamelSecondCoordinateRawAmplitude_eq_fourierPowSMulRight
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b : Fin 3)
    (ξ : H3FourierPoint3) :
    let L :
        H3FourierPoint3 →L[ℝ]
          H3FourierPoint3 →L[ℝ] ℝ :=
      -(innerSL ℝ)
    let m : Fin 2 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ]
    VectorFourier.fourierPowSMulRight
        L
        (h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i)
        ξ
        2
        m
      =
    h3SelectedDuhamelSecondCoordinateRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a b ξ := by
  dsimp only

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  have ha :
      h3FourierDerivativeSymbol a ξ
        =
      ((2 * Real.pi * inner ℝ ξ ea : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ea]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hb :
      h3FourierDerivativeSymbol b ξ
        =
      ((2 * Real.pi * inner ℝ ξ eb : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [eb]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  simp only [
    VectorFourier.fourierPowSMulRight_apply,
    Fin.prod_univ_two,
    neg_apply,
    innerSL_apply_apply ℝ,
    smul_eq_mul
  ]

  unfold h3SelectedDuhamelSecondCoordinateRawAmplitude
  rw [ha, hb]
  dsimp only [ea, eb]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- One selected Duhamel quadratic-coordinate raw amplitude reconstructs
exactly the evaluated second Fréchet derivative of the named selected Duhamel
inverse-Fourier representative. -/
theorem h3SelectedDuhamelSecondCoordinateRepresentative_eq_iteratedFDeriv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelSecondCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b)
        x
      =
    iteratedFDeriv ℝ 2
      (h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
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

  let m : Fin 2 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b)
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

  have hMom :
      ∀ (n : ℕ), n ≤ (2 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn2 : n ≤ 2 := by
      exact_mod_cast hn
    have hnCases :
        n = 0 ∨ n = 1 ∨ n = 2 := by
      omega
    rcases hnCases with rfl | rfl | rfl
    · simpa only [pow_zero, one_mul] using hAmpInt.norm
    · simpa only [pow_one] using hFirst
    · exact hSecond

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
      (n := 2)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hRawEq :
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 2 m)
        =
      h3SelectedDuhamelSecondCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b := by
    funext ξ
    dsimp only [L, f, m]
    exact
      h3SelectedDuhamelSecondCoordinateRawAmplitude_eq_fourierPowSMulRight
        ν A t hν U₀ hA hU₀ ht i a b ξ

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 2)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 2 (by norm_num))
      hMeas

  rw [
    Real.fourierIntegral_continuousMultilinearMap_apply'
      hPowInt
  ] at hEval

  rw [hRawEq] at hEval

  unfold h3SelectedDuhamelC1Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (h3SelectedDuhamelSecondCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b)
        x
      =
    iteratedFDeriv ℝ 2
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x
      m

  exact hEval.symm

/-- The same quadratic-coordinate reconstruction is the genuine second Fréchet
derivative of the literal selected classical Duhamel integral. -/
theorem h3SelectedDuhamelSecondCoordinateRepresentative_eq_C3Duhamel_iteratedFDeriv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelSecondCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b)
        x
      =
    iteratedFDeriv ℝ 2
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ] := by
  dsimp only

  have hSecond :=
    h3SelectedDuhamelSecondCoordinateRepresentative_eq_iteratedFDeriv
      hν U₀ hA hU₀ ht htR i a b x

  have hFull :=
    h3SelectedDuhamelC1Representative_eq_C3Duhamel
      hν U₀ hA hU₀ ht htR i

  dsimp only at hFull
  rw [hFull] at hSecond
  exact hSecond

end

end Euclidean
end Bridge
end PrimeTensor
