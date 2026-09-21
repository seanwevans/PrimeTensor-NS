import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quintic.Frechet.Evaluation.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quartic.Inverse.Frechet.Continuity

/-!
# Classicalization: inverse-Fourier fifth Fréchet continuity

The quintic classicalization chain now gives, for every selected difference
state,

    ‖D⁵ 𝓕(raw(W(r)-W(s)))(x)[m]‖ → 0.

The actual complex classical representative is inverse Fourier, implemented as
Fourier transform composed with spatial negation. Quintic moment integrability
makes the Fourier transform `C⁵`, and the existing linear-map chain rule gives

    D⁵ Rep(H)(x)[m]
      =
    D⁵ Fourier(raw H)(-x)[-m].

Thus the Fourier-side fifth derivative convergence transfers directly to the
actual selected complex representative.

No new estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationQuinticInverseFrechetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Quintic moment integrability makes the Fourier transform spatially `C⁵`. -/
theorem h3SpectralScalarRawFourier_fourier_contDiff_five_of_quintic
    (H : H3SpectralScalarState)
    (hFive : H3RawFourierMomentIntegrable (5 : ℝ) H) :
    ContDiff ℝ 5
      (FourierTransform.fourier
        (h3SpectralScalarRawFourier H)) := by
  apply Real.contDiff_fourier
  intro n hn
  have hn5 : n ≤ 5 := by
    exact_mod_cast hn
  exact
    h3SpectralScalarRawFourier_natMoment_integrable_le_five_of_quintic
      H hFive n hn5

/-- Exact fifth-order inverse-Fourier chain rule evaluated on an arbitrary
fixed quintuple of directions. Direction order is preserved; every direction
is negated by the right composition. -/
theorem h3SpectralScalarC1Representative_fifthFrechet_eval_eq_fourier_neg
    (H : H3SpectralScalarState)
    (hFive : H3RawFourierMomentIntegrable (5 : ℝ) H)
    (x : H3FourierPoint3)
    (m : Fin 5 → H3FourierPoint3) :
    iteratedFDeriv ℝ 5
        (h3SpectralScalarC1Representative H)
        x m
      =
    iteratedFDeriv ℝ 5
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H))
        (-x)
        (fun k => -m k) := by
  have hC5 :
      ContDiff ℝ 5
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H)) :=
    h3SpectralScalarRawFourier_fourier_contDiff_five_of_quintic
      H hFive

  rw [
    h3SpectralScalarC1Representative_eq_fourier_comp_neg
      H
  ]

  have hComp :=
    h3FourierNegCLM.iteratedFDeriv_comp_right
      hC5
      x
      (i := 5)
      (by norm_num)

  rw [hComp]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    h3FourierNegCLM_apply
  ]

/-- Along every selected coordinate path, the fifth Fréchet derivative of the
actual complex inverse-Fourier representative of the difference state,
evaluated on any fixed quintuple of directions, tends to zero at every strict
positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fifthFrechet_difference_eval_norm_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 5 → H3FourierPoint3) :
    Tendsto
      (fun r : ℝ =>
        ‖iteratedFDeriv ℝ 5
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
          ‖iteratedFDeriv ℝ 5
            (FourierTransform.fourier
              (h3SpectralScalarRawFourier
                (W r i - W s i)))
            (-x)
            (fun k => -m k)‖)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fourier_fifthFrechet_difference_eval_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i (-x) (fun k => -m k)

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEventuallyEq :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative
            (W r i - W s i))
          x m‖
          =
        ‖iteratedFDeriv ℝ 5
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (W r i - W s i)))
          (-x)
          (fun k => -m k)‖ := by
    filter_upwards [hInterval] with r hr

    have hrFiveOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        5 hν U₀ hA hU₀ hr.1 hr.2.le i

    have hsFiveOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        5 hν U₀ hA hU₀ hs hsR.le i

    have hrFive :
        H3RawFourierMomentIntegrable
          (5 : ℝ) (W r i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_five_classicalization_quinticFrechet
      ] using hrFiveOrd

    have hsFive :
        H3RawFourierMomentIntegrable
          (5 : ℝ) (W s i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_five_classicalization_quinticFrechet
      ] using hsFiveOrd

    have hDiffFive :
        H3RawFourierMomentIntegrable
          (5 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_five_sub
        (W r i) (W s i) hrFive hsFive

    rw [
      h3SpectralScalarC1Representative_fifthFrechet_eval_eq_fourier_neg
        (W r i - W s i)
        hDiffFive
        x
        m
    ]

  have hEventuallyEqRev :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 5
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (W r i - W s i)))
          (-x)
          (fun k => -m k)‖
          =
        ‖iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative
            (W r i - W s i))
          x m‖ := by
    filter_upwards [hEventuallyEq] with r hr
    exact hr.symm

  have hTarget :
      Tendsto
        (fun r : ℝ =>
          ‖iteratedFDeriv ℝ 5
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
