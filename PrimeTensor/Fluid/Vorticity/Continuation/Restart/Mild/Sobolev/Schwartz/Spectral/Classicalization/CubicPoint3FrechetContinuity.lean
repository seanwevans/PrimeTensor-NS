import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.CubicInverseFrechetContinuity

/-!
# Classicalization: Point3 third Frechet continuity

The inverse-Fourier layer now gives convergence of the complete third Frechet
derivative of the actual complex representative of the selected difference
state.

This file transports that result through the two linear maps used by the
project's real physical representative:

* `Complex.reCLM` on the left;
* the canonical `WithLp.toLp 2` spatial identification on the right.

The result is third-Frechet continuity, evaluated on arbitrary fixed `Point3`
directions, for

    h3SpectralScalarRealC1RepresentativeOnPoint3.

No coordinate partials are introduced here.  The next increment is therefore
purely Euclidean: identify a nested ordered `spatial3.d` triple with this
third Frechet derivative evaluated on `axisDirection`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationCubicPoint3FrechetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- The canonical linear identification from the project's ordinary spatial
carrier to the Fourier `PiLp 2` carrier. -/
noncomputable def h3Point3ToFourierCLM :
    Point3 →L[ℝ] H3FourierPoint3 :=
  (PiLp.continuousLinearEquiv
      2
      ℝ
      (fun _ : PrimeTensor.Axis Depth.three => ℝ)).symm.toContinuousLinearMap

@[simp]
theorem h3Point3ToFourierCLM_apply
    (x : Point3) :
    h3Point3ToFourierCLM x
      =
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x := by
  rfl

/-- Cubic moment integrability upgrades the actual complex inverse-Fourier
representative to spatial `C³`. -/
theorem h3SpectralScalarC1Representative_contDiff_three_of_cubic
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H) :
    ContDiff ℝ 3
      (h3SpectralScalarC1Representative H) := by
  rw [
    h3SpectralScalarC1Representative_eq_fourier_comp_neg
      H
  ]

  exact
    (h3SpectralScalarRawFourier_fourier_contDiff_three_of_cubic
      H hThree).comp_continuousLinearMap

/-- Taking real parts preserves the cubic regularity supplied by the moment
hypothesis. -/
theorem h3SpectralScalarRealC1Representative_contDiff_three_of_cubic
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H) :
    ContDiff ℝ 3
      (h3SpectralScalarRealC1Representative H) := by
  unfold h3SpectralScalarRealC1Representative

  simpa [Function.comp_def] using
    (h3SpectralScalarC1Representative_contDiff_three_of_cubic
      H hThree).continuousLinearMap_comp
        Complex.reCLM

/-- The real `Point3` representative is the composition of the real Fourier
carrier representative with the canonical continuous linear `PiLp` map. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_eq_comp
    (H : H3SpectralScalarState) :
    h3SpectralScalarRealC1RepresentativeOnPoint3 H
      =
    h3SpectralScalarRealC1Representative H
      ∘
    h3Point3ToFourierCLM := by
  funext x
  unfold h3SpectralScalarRealC1RepresentativeOnPoint3
  simp only [Function.comp_apply, h3Point3ToFourierCLM_apply]

/-- Exact third-order chain rule through real-part extraction and the canonical
`Point3 → H3FourierPoint3` linear map.

The order of the three directions is unchanged. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_thirdFrechet_eval_eq_re
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H)
    (x : Point3)
    (m : Fin 3 → Point3) :
    iteratedFDeriv ℝ 3
        (h3SpectralScalarRealC1RepresentativeOnPoint3 H)
        x m
      =
    (iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative H)
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))).re := by
  have hComplexC3 :
      ContDiff ℝ 3
        (h3SpectralScalarC1Representative H) :=
    h3SpectralScalarC1Representative_contDiff_three_of_cubic
      H hThree

  have hRealC3 :
      ContDiff ℝ 3
        (h3SpectralScalarRealC1Representative H) :=
    h3SpectralScalarRealC1Representative_contDiff_three_of_cubic
      H hThree

  have hLeft :
      iteratedFDeriv ℝ 3
          (h3SpectralScalarRealC1Representative H)
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative H)
          (h3Point3ToFourierCLM x)) := by
    unfold h3SpectralScalarRealC1Representative
    change
      iteratedFDeriv ℝ 3
          (Complex.reCLM ∘
            h3SpectralScalarC1Representative H)
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative H)
          (h3Point3ToFourierCLM x))

    exact
      Complex.reCLM.iteratedFDeriv_comp_left
        hComplexC3.contDiffAt
        (by norm_num)

  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_eq_comp
      H
  ]

  have hRight :=
    h3Point3ToFourierCLM.iteratedFDeriv_comp_right
      hRealC3
      x
      (i := 3)
      (by norm_num)

  rw [hRight]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply
  ]

  rw [hLeft]

  rfl

/-- Along every selected coordinate path, the complete third Frechet
derivative of the real `Point3` representative of the difference state,
evaluated on any fixed triple of ordinary spatial directions, tends to zero at
each strict positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_thirdFrechet_difference_eval_norm_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (m : Fin 3 → Point3) :
    Tendsto
      (fun r : ℝ =>
        ‖iteratedFDeriv ℝ 3
          (h3SpectralScalarRealC1RepresentativeOnPoint3
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

  have hComplex :
      Tendsto
        (fun r : ℝ =>
          ‖iteratedFDeriv ℝ 3
            (h3SpectralScalarC1Representative
              (W r i - W s i))
            (h3Point3ToFourierCLM x)
            (fun k => h3Point3ToFourierCLM (m k))‖)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_thirdFrechet_difference_eval_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  refine tendsto_order.2 ⟨?_, ?_⟩

  · intro c hc
    exact Filter.Eventually.of_forall (fun r =>
      lt_of_lt_of_le hc (norm_nonneg _))

  · intro ε hε

    have hComplexEventually :
        ∀ᶠ r in 𝓝 s,
          ‖iteratedFDeriv ℝ 3
            (h3SpectralScalarC1Representative
              (W r i - W s i))
            (h3Point3ToFourierCLM x)
            (fun k => h3Point3ToFourierCLM (m k))‖
            < ε :=
      (tendsto_order.1 hComplex).2 ε hε

    filter_upwards
      [hInterval, hComplexEventually]
      with r hr hComplexLt

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
      h3SpectralScalarRealC1RepresentativeOnPoint3_thirdFrechet_eval_eq_re
        (W r i - W s i)
        hDiffThree
        x
        m
    ]

    let z : ℂ :=
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (W r i - W s i))
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))

    have hRe :
        ‖z.re‖ ≤ ‖z‖ := by
      simpa [Real.norm_eq_abs] using
        Complex.abs_re_le_norm z

    exact
      lt_of_le_of_lt
        hRe
        hComplexLt

end
end Euclidean
end Bridge
end PrimeTensor
