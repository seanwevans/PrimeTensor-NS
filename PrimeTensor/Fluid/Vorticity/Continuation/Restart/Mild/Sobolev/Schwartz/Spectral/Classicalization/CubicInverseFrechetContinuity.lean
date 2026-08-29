import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.CubicFrechetEvaluationContinuity

/-!
# Classicalization: inverse-Fourier third Frechet continuity

The preceding classicalization layers establish cubic weighted Fourier
continuity, convert it to operator-norm continuity of the complete third
Frechet derivative of the Fourier transform, and then evaluate that
multilinear map on an arbitrary fixed triple of directions.

This file closes the inverse-Fourier chain-rule step for the project's actual
complex classical representative

    h3SpectralScalarC1Representative H
      = fun x => FourierTransform.fourier (raw H) (-x).

Since spatial negation is a continuous linear map, Mathlib's
`ContinuousLinearMap.iteratedFDeriv_comp_right` gives the exact third-order
formula: the inverse-Fourier third derivative at `x`, evaluated on directions
`m`, is the Fourier third derivative at `-x`, evaluated on the negated
directions.

Thus the already-compiled Fourier-side convergence immediately becomes
third-Frechet continuity of the actual inverse-Fourier representative of the
selected difference state.

The remaining transport is now only:
* compose on the left with `Complex.reCLM`;
* compose on the right with the canonical `WithLp.toLp 2` spatial map;
* evaluate on `axisDirection` to identify the ordered `spatial3.d` jet.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationCubicInverseFrechetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Spatial negation on the Fourier carrier as a continuous linear map. -/
noncomputable def h3FourierNegCLM :
    H3FourierPoint3 →L[ℝ] H3FourierPoint3 :=
  -ContinuousLinearMap.id ℝ H3FourierPoint3

@[simp]
theorem h3FourierNegCLM_apply
    (x : H3FourierPoint3) :
    h3FourierNegCLM x = -x := by
  rfl

/-- Cubic moment integrability is enough to make the Fourier transform `C³`,
using the lower-moment bridge already compiled in `CubicFrechetContinuity`. -/
theorem h3SpectralScalarRawFourier_fourier_contDiff_three_of_cubic
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H) :
    ContDiff ℝ 3
      (FourierTransform.fourier
        (h3SpectralScalarRawFourier H)) := by
  apply Real.contDiff_fourier
  intro n hn
  have hn3 : n ≤ 3 := by
    exact_mod_cast hn
  exact
    h3SpectralScalarRawFourier_natMoment_integrable_le_three_of_cubic
      H hThree n hn3

/-- The project inverse-Fourier representative is literally Fourier transform
after spatial negation. -/
theorem h3SpectralScalarC1Representative_eq_fourier_comp_neg
    (H : H3SpectralScalarState) :
    h3SpectralScalarC1Representative H
      =
    FourierTransform.fourier
        (h3SpectralScalarRawFourier H)
      ∘
    h3FourierNegCLM := by
  funext x
  unfold h3SpectralScalarC1Representative
  change
    FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourier H) x
      =
    FourierTransform.fourier
        (h3SpectralScalarRawFourier H)
        (-x)
  exact
    Real.fourierInv_eq_fourier_neg
      (h3SpectralScalarRawFourier H) x

/-- Exact third-order inverse-Fourier chain rule, evaluated on an arbitrary
fixed triple of directions.

No symmetry or mixed-partial permutation is used: the direction order is
preserved and every direction is simply negated by the right composition. -/
theorem h3SpectralScalarC1Representative_thirdFrechet_eval_eq_fourier_neg
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H)
    (x : H3FourierPoint3)
    (m : Fin 3 → H3FourierPoint3) :
    iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative H)
        x m
      =
    iteratedFDeriv ℝ 3
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H))
        (-x)
        (fun k => -m k) := by
  have hC3 :
      ContDiff ℝ 3
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H)) :=
    h3SpectralScalarRawFourier_fourier_contDiff_three_of_cubic
      H hThree

  rw [
    h3SpectralScalarC1Representative_eq_fourier_comp_neg
      H
  ]

  have hComp :=
    h3FourierNegCLM.iteratedFDeriv_comp_right
      hC3
      x
      (i := 3)
      (by norm_num)

  rw [hComp]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    h3FourierNegCLM_apply
  ]

/-- Along every selected coordinate path, the third Frechet derivative of the
actual complex inverse-Fourier representative of the difference state,
evaluated on any fixed triple of directions, tends to zero at every strict
positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_thirdFrechet_difference_eval_norm_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 3 → H3FourierPoint3) :
    Tendsto
      (fun r : ℝ =>
        ‖iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ r i
              -
              h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ s i))
          x m‖)
      (𝓝 s)
      (𝓝 0) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hFourier :
      Tendsto
        (fun r : ℝ =>
          ‖iteratedFDeriv ℝ 3
            (FourierTransform.fourier
              (h3SpectralScalarRawFourier
                (W r i - W s i)))
            (-x)
            (fun k => -m k)‖)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fourier_thirdFrechet_difference_eval_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i (-x) (fun k => -m k)

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEventuallyEq :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative
            (W r i - W s i))
          x m‖
          =
        ‖iteratedFDeriv ℝ 3
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (W r i - W s i)))
          (-x)
          (fun k => -m k)‖ := by
    filter_upwards [hInterval] with r hr

    have hrThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hr.1 hr.2.le i

    have hsThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hs hsR.le i

    have hrThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_three_classicalization_cubicFrechet
      ] using hrThreeOrd

    have hsThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W s i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_three_classicalization_cubicFrechet
      ] using hsThreeOrd

    have hDiffThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_three_sub
        (W r i) (W s i) hrThree hsThree

    rw [
      h3SpectralScalarC1Representative_thirdFrechet_eval_eq_fourier_neg
        (W r i - W s i)
        hDiffThree
        x
        m
    ]

  have hEventuallyEqRev :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 3
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (W r i - W s i)))
          (-x)
          (fun k => -m k)‖
          =
        ‖iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative
            (W r i - W s i))
          x m‖ := by
    filter_upwards [hEventuallyEq] with r hr
    exact hr.symm

  have hTarget :
      Tendsto
        (fun r : ℝ =>
          ‖iteratedFDeriv ℝ 3
            (h3SpectralScalarC1Representative
              (W r i - W s i))
            x m‖)
        (𝓝 s)
        (𝓝 0) :=
    hFourier.congr' hEventuallyEqRev

  simpa only [W] using hTarget

end
end Euclidean
end Bridge
end PrimeTensor
