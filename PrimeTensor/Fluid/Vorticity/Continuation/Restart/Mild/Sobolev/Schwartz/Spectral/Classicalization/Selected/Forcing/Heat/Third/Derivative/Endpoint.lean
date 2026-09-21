import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C3.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Third.Endpoint.Frozen
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Endpoint.Continuity
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Classicalization: selected forcing third-derivative heat endpoint

The cubic forcing-difference topology is now available.  To convert it into
time continuity of the genuine third spatial Fréchet jet, this file exposes
the zero-heat-lag ordered third-coordinate reconstruction.

For canonical directions `a,b,c`, define

    d_a(ξ) d_b(ξ) d_c(ξ) H_τ N̂(ξ),

reconstruct it by ordinary inverse Fourier transform, and then specialize to
`τ = 0`.

At a strict positive selected restart time the instantaneous forcing already
has an integrable cubic raw Fourier moment.  Hence the zero-lag cubic
multiplier is Fourier `L¹`, and Mathlib's explicit iterated Fourier derivative
formula identifies its inverse-Fourier reconstruction with

    D³ N[e_a,e_b,e_c].

No temporal estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingHeatThirdDerivativeEndpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Inverse-Fourier reconstruction of one ordered third-coordinate derivative
of the heat-regularized nonlinear forcing. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i a b c : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
      ν τ U V i a b c)

/-- At a selected positive restart time, three coordinate multipliers of the
unheated raw forcing are genuinely Fourier `L¹`. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_thirdCoordinate_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ *
              h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ)))
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  have hZero :
      Integrable F
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hThird :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ *
              (h3FourierDerivativeSymbol c ξ * F ξ)))
        (volume : Measure H3FourierPoint3) :=
    (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
      ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous c).aestronglyMeasurable.mul
          hZero.aestronglyMeasurable))

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 3 *
            (‖ξ‖ ^ 3 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hThird.const_mul ((2 * Real.pi) ^ 3)

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hAmp :=
    norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude_le_thirdMoment
      ν 0 (W t) (W t) i a b c ξ

  unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude at hAmp
  rw [
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
      ν (W t) (W t) i
  ] at hAmp

  simpa only [F] using hAmp

/-- At zero heat lag, the ordered third-coordinate reconstruction is exactly
the genuine third Fréchet derivative of the selected instantaneous forcing. -/
theorem h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
        ν 0 (W t) (W t) i a b c x
      =
    iteratedFDeriv ℝ 3
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c)
      ] := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 3 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c)
    ]

  have hZero :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hOne :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hTwo :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hThree :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMoment_integrable
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
    · simpa only [pow_zero, one_mul] using hZero.norm
    · simpa only [pow_one] using hOne
    · exact hTwo
    · exact hThree

  have hMeas :
      AEStronglyMeasurable
        f
        (volume : Measure H3FourierPoint3) :=
    hZero.aestronglyMeasurable

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
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ * f ξ))) := by
    funext ξ

    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let ec : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 c)

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

    have hc :
        h3FourierDerivativeSymbol c ξ
          =
        ((2 * Real.pi * inner ℝ ξ ec : ℝ) : ℂ) *
          Complex.I := by
      dsimp only [ec]
      rw [h3FourierDerivativeSymbol_eq_inner]
      push_cast
      ring

    dsimp only [L, m]
    simp only [
      VectorFourier.fourierPowSMulRight_apply,
      Fin.prod_univ_three,
      neg_apply,
      innerSL_apply_apply ℝ,
      smul_eq_mul
    ]
    rw [ha, hb, hc]
    dsimp only [ea, eb, ec]
    simp [Complex.real_smul] <;> push_cast <;> ring

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

  have hHeatZero :
      (fun ξ : H3FourierPoint3 =>
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          ν 0 (W t) (W t) i a b c ξ)
        =
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ * f ξ))) := by
    funext ξ
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W t) (W t) i
    ]

  unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative

  change
    FourierTransformInv.fourierInv
      (fun ξ : H3FourierPoint3 =>
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          ν 0 (W t) (W t) i a b c ξ)
      x
      =
    iteratedFDeriv ℝ 3
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      x
      m

  rw [hHeatZero]

  unfold h3RawFinLerayOuterProductDivergenceC0Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ *
              (h3FourierDerivativeSymbol c ξ * f ξ)))
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

end

end Euclidean
end Bridge
end PrimeTensor
