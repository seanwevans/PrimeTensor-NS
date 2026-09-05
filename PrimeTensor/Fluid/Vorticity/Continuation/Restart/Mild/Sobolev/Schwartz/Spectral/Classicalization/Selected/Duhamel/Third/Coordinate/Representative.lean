import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.History.Generator.Raw.Trace
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullPointwise
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Derivative

/-!
# Classicalization: selected Duhamel third-coordinate reconstruction

The old-history first-Fréchet generator has now been reduced at the raw Fourier
level to

    ν * Σ_k d_a d_k d_k A_t,

where `A_t` is the named selected Duhamel raw amplitude.

This file identifies one ordered cubic multiplier

    d_a d_k d_l A_t

with the genuine third spatial Fréchet derivative of the selected classical
Duhamel reconstruction evaluated on the corresponding coordinate directions.

The proof is the same canonical Fourier differentiation argument already used
for the positive-time heat third-coordinate representative.  For the named
selected Duhamel amplitude, the required moments through order three are:

* order 0: the existing raw `L¹` reconstruction theorem;
* order 1: the generic H³ first moment, transported across the selected raw
  a.e. representative bridge;
* order 2: the existing selected Duhamel second-moment theorem;
* order 3: the cubic selected Duhamel moment already transported to the named
  raw amplitude.

No mixed spatial/time derivative is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdCoordinateRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The selected Duhamel cubic coordinate multiplier is exactly Mathlib's
order-three inverse-Fourier multiplier on the corresponding canonical
coordinate directions. -/
theorem h3SelectedDuhamelThirdCoordinateRawAmplitude_eq_fourierPowSMulRight
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a k l : Fin 3)
    (ξ : H3FourierPoint3) :
    let L :
        H3FourierPoint3 →L[ℝ]
          H3FourierPoint3 →L[ℝ] ℝ :=
      -(innerSL ℝ)
    let m : Fin 3 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 k),
        h3FourierAxisDirection (h3AxisOfFin3 l)
      ]
    VectorFourier.fourierPowSMulRight
        L
        (h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i)
        ξ
        3
        m
      =
    h3SelectedDuhamelThirdCoordinateRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a k l ξ := by
  dsimp only

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)
  let ek : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 k)
  let el : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 l)

  have ha :
      h3FourierDerivativeSymbol a ξ
        =
      ((2 * Real.pi * inner ℝ ξ ea : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ea]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hk :
      h3FourierDerivativeSymbol k ξ
        =
      ((2 * Real.pi * inner ℝ ξ ek : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ek]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hl :
      h3FourierDerivativeSymbol l ξ
        =
      ((2 * Real.pi * inner ℝ ξ el : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [el]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  simp only [
    VectorFourier.fourierPowSMulRight_apply,
    Fin.prod_univ_three,
    neg_apply,
    innerSL_apply_apply ℝ,
    smul_eq_mul
  ]

  unfold h3SelectedDuhamelThirdCoordinateRawAmplitude
  rw [ha, hk, hl]
  dsimp only [ea, ek, el]
  simp [Complex.real_smul] <;> push_cast <;> ring

/-- One selected Duhamel cubic-coordinate raw amplitude reconstructs exactly
the evaluated third Fréchet derivative of the named selected Duhamel inverse
Fourier representative. -/
theorem h3SelectedDuhamelThirdCoordinateRepresentative_eq_iteratedFDeriv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a k l : Fin 3)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelThirdCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a k l)
        x
      =
    iteratedFDeriv ℝ 3
      (h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 k),
        h3FourierAxisDirection (h3AxisOfFin3 l)
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

  let m : Fin 3 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 k),
      h3FourierAxisDirection (h3AxisOfFin3 l)
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
      Integrable f (volume : Measure H3FourierPoint3) := by
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

  have hMom :
      ∀ (n : ℕ), n ≤ (3 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn3 : n ≤ 3 := by
      exact_mod_cast hn
    have hnCases :
        n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
      omega
    rcases hnCases with rfl | rfl | rfl | rfl
    · simpa only [pow_zero, one_mul] using hAmpInt.norm
    · simpa only [pow_one] using hFirst
    · exact hSecond
    · exact hThird

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
      (n := 3)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hRawEq :
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 3 m)
        =
      h3SelectedDuhamelThirdCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a k l := by
    funext ξ
    dsimp only [L, f, m]
    exact
      h3SelectedDuhamelThirdCoordinateRawAmplitude_eq_fourierPowSMulRight
        ν A t hν U₀ hA hU₀ ht i a k l ξ

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 3)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 3 (by norm_num))
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
        (h3SelectedDuhamelThirdCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a k l)
        x
      =
    iteratedFDeriv ℝ 3
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x
      m

  exact hEval.symm

/-- The same cubic-coordinate reconstruction is the genuine third Fréchet
derivative of the literal selected classical Duhamel integral. -/
theorem h3SelectedDuhamelThirdCoordinateRepresentative_eq_C3Duhamel_iteratedFDeriv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a k l : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelThirdCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a k l)
        x
      =
    iteratedFDeriv ℝ 3
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 k),
        h3FourierAxisDirection (h3AxisOfFin3 l)
      ] := by
  dsimp only

  have hThird :=
    h3SelectedDuhamelThirdCoordinateRepresentative_eq_iteratedFDeriv
      hν U₀ hA hU₀ ht htR i a k l x

  have hFull :=
    h3SelectedDuhamelC1Representative_eq_C3Duhamel
      hν U₀ hA hU₀ ht htR i

  dsimp only at hFull
  rw [hFull] at hThird
  exact hThird

end

end Euclidean
end Bridge
end PrimeTensor
