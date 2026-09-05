import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Point3.Gradient.Time.Continuity

/-!
# Classicalization: real Point3 forcing gradient time continuity

The selected instantaneous forcing gradient is now time-continuous on the
complex `Point3` representative.

The real physical forcing is obtained by postcomposing that representative
with the fixed continuous linear map `Complex.reCLM`.  Postcomposition by a
fixed continuous linear map is continuous on operator spaces.  On the positive
restart interval, the spatial `C¹` theorem identifies the resulting operator
with the actual Fréchet derivative of the real-part forcing.

Thus the real `Point3` forcing gradient is time-continuous at every strict
positive interior restart time.  No new nonlinear estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingRealPoint3GradientTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The spatial Fréchet derivative of the real selected instantaneous forcing
on `Point3` is time-continuous at every strict positive interior restart time. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_fderiv_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        fderiv ℝ
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W r) (W r) i y).re)
          x)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let P : ℝ → Point3 → ℂ :=
    fun r =>
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W r) (W r) i

  let C : ℝ → (Point3 →L[ℝ] ℂ) :=
    fun r =>
      fderiv ℝ (P r) x

  let R : ℝ → (Point3 →L[ℝ] ℝ) :=
    fun r =>
      Complex.reCLM.comp (C r)

  have hC :
      ContinuousAt C s := by
    dsimp only [C, P, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_fderiv_continuousAt_time
        hν U₀ hA hU₀ hs hsR i x

  have hR :
      ContinuousAt R s := by
    change
      ContinuousAt
        ((ContinuousLinearMap.postcomp Point3 Complex.reCLM) ∘ C)
        s
    exact
      ((ContinuousLinearMap.postcomp Point3 Complex.reCLM).continuous.continuousAt).comp
        hC

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEq :
      (fun r : ℝ =>
        fderiv ℝ
          (fun y : Point3 => (P r y).re)
          x)
        =ᶠ[𝓝 s]
      R := by
    filter_upwards [hInterval] with r hr

    have hPContDiff :
        ContDiff ℝ 1 (P r) := by
      dsimp only [P, W]
      exact
        h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_contDiff_one
          hν U₀ hA hU₀ hr.1 hr.2.le i

    have hPDiff :
        DifferentiableAt ℝ (P r) x := by
      exact
        (hPContDiff.differentiable (by norm_num)).differentiableAt

    dsimp only [R, C]

    change
      fderiv ℝ
          (Complex.reCLM ∘ P r)
          x
        =
      Complex.reCLM.comp
        (fderiv ℝ (P r) x)

    rw [fderiv_comp x Complex.reCLM.differentiableAt hPDiff]

    simp

  exact
    hR.congr_of_eventuallyEq hEq

end

end Euclidean
end Bridge
end PrimeTensor
