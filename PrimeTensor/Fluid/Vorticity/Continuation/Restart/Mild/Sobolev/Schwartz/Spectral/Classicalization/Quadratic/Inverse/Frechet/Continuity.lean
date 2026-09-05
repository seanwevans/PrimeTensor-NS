import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quadratic.Frechet.Evaluation.Continuity

/-!
# Classicalization: inverse-Fourier second Frechet continuity

The quadratic classicalization chain now gives:

* quadratic weighted raw-Fourier continuity of the selected difference state;
* operator-norm continuity of the complete second Frechet derivative of the
  ordinary Fourier transform;
* convergence after evaluation on an arbitrary fixed pair of directions.

This file closes the inverse-Fourier chain-rule step for the project's actual
complex classical representative

    h3SpectralScalarC1Representative H
      = fun x => FourierTransform.fourier (raw H) (-x).

Spatial negation is a continuous linear map.  Therefore Mathlib's
`ContinuousLinearMap.iteratedFDeriv_comp_right` gives the exact second-order
formula: the inverse-Fourier second derivative at `x`, evaluated on directions
`m`, is the Fourier second derivative at `-x`, evaluated on the negated
directions.

Thus the already-compiled Fourier-side convergence immediately becomes
second-Frechet continuity of the actual inverse-Fourier representative of the
selected difference state.

The remaining step toward the temporal derivative candidate is now only the
finite-dimensional identification with the Hessian/second-coordinate
evaluation used by the Duhamel generator.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationQuadraticInverseFrechetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Spatial negation on the Fourier carrier, kept local to the quadratic
classicalization chain so this module does not depend on the cubic inverse
bridge. -/
noncomputable def h3QuadraticFourierNegCLM :
    H3FourierPoint3 →L[ℝ] H3FourierPoint3 :=
  -ContinuousLinearMap.id ℝ H3FourierPoint3

@[simp]
theorem h3QuadraticFourierNegCLM_apply
    (x : H3FourierPoint3) :
    h3QuadraticFourierNegCLM x = -x := by
  rfl

/-- Quadratic moment integrability is enough to make the Fourier transform
`C²`, using the lower-moment bridge already compiled in
`QuadraticFrechetContinuity`. -/
theorem h3SpectralScalarRawFourier_fourier_contDiff_two_of_quadratic
    (H : H3SpectralScalarState)
    (hTwo : H3RawFourierMomentIntegrable (2 : ℝ) H) :
    ContDiff ℝ 2
      (FourierTransform.fourier
        (h3SpectralScalarRawFourier H)) := by
  apply Real.contDiff_fourier
  intro n hn
  have hn2 : n ≤ 2 := by
    exact_mod_cast hn
  exact
    h3SpectralScalarRawFourier_natMoment_integrable_le_two_of_quadratic
      H hTwo n hn2

/-- The project inverse-Fourier representative is literally Fourier transform
after spatial negation. -/
theorem h3SpectralScalarC1Representative_eq_fourier_comp_neg_quadratic
    (H : H3SpectralScalarState) :
    h3SpectralScalarC1Representative H
      =
    FourierTransform.fourier
        (h3SpectralScalarRawFourier H)
      ∘
    h3QuadraticFourierNegCLM := by
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

/-- Exact second-order inverse-Fourier chain rule, evaluated on an arbitrary
fixed pair of directions.  The direction order is preserved and each
direction is negated by the right composition. -/
theorem h3SpectralScalarC1Representative_secondFrechet_eval_eq_fourier_neg
    (H : H3SpectralScalarState)
    (hTwo : H3RawFourierMomentIntegrable (2 : ℝ) H)
    (x : H3FourierPoint3)
    (m : Fin 2 → H3FourierPoint3) :
    iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative H)
        x m
      =
    iteratedFDeriv ℝ 2
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H))
        (-x)
        (fun k => -m k) := by
  have hC2 :
      ContDiff ℝ 2
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H)) :=
    h3SpectralScalarRawFourier_fourier_contDiff_two_of_quadratic
      H hTwo

  rw [
    h3SpectralScalarC1Representative_eq_fourier_comp_neg_quadratic
      H
  ]

  have hComp :=
    h3QuadraticFourierNegCLM.iteratedFDeriv_comp_right
      hC2
      x
      (i := 2)
      (by norm_num)

  rw [hComp]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    h3QuadraticFourierNegCLM_apply
  ]

/-- Along every selected coordinate path, the second Frechet derivative of the
actual complex inverse-Fourier representative of the difference state,
evaluated on any fixed pair of directions, tends to zero at every strict
positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_secondFrechet_difference_eval_norm_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 2 → H3FourierPoint3) :
    Tendsto
      (fun r : ℝ =>
        ‖iteratedFDeriv ℝ 2
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
          ‖iteratedFDeriv ℝ 2
            (FourierTransform.fourier
              (h3SpectralScalarRawFourier
                (W r i - W s i)))
            (-x)
            (fun k => -m k)‖)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fourier_secondFrechet_difference_eval_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i (-x) (fun k => -m k)

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEventuallyEq :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative
            (W r i - W s i))
          x m‖
          =
        ‖iteratedFDeriv ℝ 2
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
      refine hrThreeOrd.congr ?_
      filter_upwards with ξ
      have hWeight3 :
          h3FourierMomentWeight (3 : ℝ) ξ = ‖ξ‖ ^ 3 := by
        have h := h3FourierMomentWeight_natCast 3 ξ
        norm_num at h
        exact h
      dsimp only [W]
      rw [hWeight3]

    have hsThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W s i) := by
      unfold H3RawFourierMomentIntegrable
      refine hsThreeOrd.congr ?_
      filter_upwards with ξ
      have hWeight3 :
          h3FourierMomentWeight (3 : ℝ) ξ = ‖ξ‖ ^ 3 := by
        have h := h3FourierMomentWeight_natCast 3 ξ
        norm_num at h
        exact h
      dsimp only [W]
      rw [hWeight3]

    have hDiffThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_three_sub
        (W r i) (W s i) hrThree hsThree

    have hDiffTwo :
        H3RawFourierMomentIntegrable
          (2 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_two_of_three
        (W r i - W s i) hDiffThree

    rw [
      h3SpectralScalarC1Representative_secondFrechet_eval_eq_fourier_neg
        (W r i - W s i)
        hDiffTwo
        x
        m
    ]

  have hEventuallyEqRev :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 2
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (W r i - W s i)))
          (-x)
          (fun k => -m k)‖
          =
        ‖iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative
            (W r i - W s i))
          x m‖ := by
    filter_upwards [hEventuallyEq] with r hr
    exact hr.symm

  have hTarget :
      Tendsto
        (fun r : ℝ =>
          ‖iteratedFDeriv ℝ 2
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
