import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quartic.Frechet.Evaluation.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Inverse.Frechet.Continuity

/-!
# Classicalization: inverse-Fourier fourth Fréchet continuity

The quartic classicalization chain now gives, for every selected difference
state,

    ‖D⁴ 𝓕(raw(W(r)-W(s)))(x)[m]‖ → 0.

The project's actual complex classical representative is inverse Fourier:

    h3SpectralScalarC1Representative H
      = fun x => FourierTransform.fourier (raw H) (-x).

The spatial-negation continuous linear map and this exact representative
identity were already compiled in the cubic inverse-Fourier layer.

This file lifts them one order. Quartic moment integrability makes the Fourier
transform `C⁴`, and
`ContinuousLinearMap.iteratedFDeriv_comp_right` identifies

    D⁴ Rep(H)(x)[m]
      =
    D⁴ Fourier(raw H)(-x)[-m].

Thus the already-compiled Fourier-side fourth derivative convergence transfers
directly to the actual inverse-Fourier representative.

No new estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationQuarticInverseFrechetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Quartic moment integrability makes the Fourier transform spatially `C⁴`. -/
theorem h3SpectralScalarRawFourier_fourier_contDiff_four_of_quartic
    (H : H3SpectralScalarState)
    (hFour : H3RawFourierMomentIntegrable (4 : ℝ) H) :
    ContDiff ℝ 4
      (FourierTransform.fourier
        (h3SpectralScalarRawFourier H)) := by
  apply Real.contDiff_fourier
  intro n hn
  have hn4 : n ≤ 4 := by
    exact_mod_cast hn
  exact
    h3SpectralScalarRawFourier_natMoment_integrable_le_four_of_quartic
      H hFour n hn4

/-- Exact fourth-order inverse-Fourier chain rule evaluated on an arbitrary
fixed quadruple of directions. Direction order is preserved; every direction
is simply negated by the right composition. -/
theorem h3SpectralScalarC1Representative_fourthFrechet_eval_eq_fourier_neg
    (H : H3SpectralScalarState)
    (hFour : H3RawFourierMomentIntegrable (4 : ℝ) H)
    (x : H3FourierPoint3)
    (m : Fin 4 → H3FourierPoint3) :
    iteratedFDeriv ℝ 4
        (h3SpectralScalarC1Representative H)
        x m
      =
    iteratedFDeriv ℝ 4
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H))
        (-x)
        (fun k => -m k) := by
  have hC4 :
      ContDiff ℝ 4
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H)) :=
    h3SpectralScalarRawFourier_fourier_contDiff_four_of_quartic
      H hFour

  rw [
    h3SpectralScalarC1Representative_eq_fourier_comp_neg
      H
  ]

  have hComp :=
    h3FourierNegCLM.iteratedFDeriv_comp_right
      hC4
      x
      (i := 4)
      (by norm_num)

  rw [hComp]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    h3FourierNegCLM_apply
  ]

/-- Along every selected coordinate path, the fourth Fréchet derivative of the
actual complex inverse-Fourier representative of the difference state,
evaluated on any fixed quadruple of directions, tends to zero at every strict
positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fourthFrechet_difference_eval_norm_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 4 → H3FourierPoint3) :
    Tendsto
      (fun r : ℝ =>
        ‖iteratedFDeriv ℝ 4
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
          ‖iteratedFDeriv ℝ 4
            (FourierTransform.fourier
              (h3SpectralScalarRawFourier
                (W r i - W s i)))
            (-x)
            (fun k => -m k)‖)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fourier_fourthFrechet_difference_eval_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i (-x) (fun k => -m k)

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEventuallyEq :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 4
          (h3SpectralScalarC1Representative
            (W r i - W s i))
          x m‖
          =
        ‖iteratedFDeriv ℝ 4
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (W r i - W s i)))
          (-x)
          (fun k => -m k)‖ := by
    filter_upwards [hInterval] with r hr

    have hrFourOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        4 hν U₀ hA hU₀ hr.1 hr.2.le i

    have hsFourOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        4 hν U₀ hA hU₀ hs hsR.le i

    have hrFour :
        H3RawFourierMomentIntegrable
          (4 : ℝ) (W r i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_four_classicalization_quarticFrechet
      ] using hrFourOrd

    have hsFour :
        H3RawFourierMomentIntegrable
          (4 : ℝ) (W s i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_four_classicalization_quarticFrechet
      ] using hsFourOrd

    have hDiffFour :
        H3RawFourierMomentIntegrable
          (4 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_four_sub
        (W r i) (W s i) hrFour hsFour

    rw [
      h3SpectralScalarC1Representative_fourthFrechet_eval_eq_fourier_neg
        (W r i - W s i)
        hDiffFour
        x
        m
    ]

  have hEventuallyEqRev :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 4
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (W r i - W s i)))
          (-x)
          (fun k => -m k)‖
          =
        ‖iteratedFDeriv ℝ 4
          (h3SpectralScalarC1Representative
            (W r i - W s i))
          x m‖ := by
    filter_upwards [hEventuallyEq] with r hr
    exact hr.symm

  have hTarget :
      Tendsto
        (fun r : ℝ =>
          ‖iteratedFDeriv ℝ 4
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
