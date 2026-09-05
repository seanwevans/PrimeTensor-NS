import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Gradient.Time.Continuity

/-!
# Classicalization: Point3 forcing gradient time continuity

The previous layer proves time continuity of the Fréchet derivative of the
selected instantaneous forcing on the Fourier Euclidean carrier.

The project-facing forcing representative lives on `Point3`, obtained by
precomposition with the fixed linear equivalence `WithLp.toLp 2`.

For every positive restart time,

    D (N_t ∘ toLp)(x)
      = D N_t(toLp x) ∘ D(toLp)(x).

The second factor is fixed in time.  Precomposition by a fixed continuous
linear map is itself a continuous linear map on operator spaces, so continuity
of `D N_t(toLp x)` transports directly to the `Point3` derivative.

No new estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingPoint3GradientTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The Fréchet derivative of the selected instantaneous complex forcing on
`Point3` is time-continuous at every strict positive interior restart time. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_fderiv_continuousAt_time
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
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W r) (W r) i)
          x)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let toLp : Point3 → H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3)

  let G : ℝ → H3FourierPoint3 → ℂ :=
    fun r =>
      h3RawFinLerayOuterProductDivergenceC0Representative
        (W r) (W r) i

  let P : ℝ → Point3 → ℂ :=
    fun r =>
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W r) (W r) i

  let Aop : ℝ → (H3FourierPoint3 →L[ℝ] ℂ) :=
    fun r =>
      fderiv ℝ (G r) (toLp x)

  let L : Point3 →L[ℝ] H3FourierPoint3 :=
    fderiv ℝ toLp x

  let Bop : ℝ → (Point3 →L[ℝ] ℂ) :=
    fun r => (Aop r).comp L

  have hAop :
      ContinuousAt Aop s := by
    dsimp only [Aop, G, toLp, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_fderiv_continuousAt_time
        hν U₀ hA hU₀ hs hsR i
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  have hBop :
      ContinuousAt Bop s := by
    change
      ContinuousAt
        ((ContinuousLinearMap.precomp ℂ L) ∘ Aop)
        s
    exact
      ((ContinuousLinearMap.precomp ℂ L).continuous.continuousAt).comp
        hAop

  have hToLpContDiff :
      ContDiff ℝ 1 toLp := by
    dsimp only [toLp]
    exact
      (PiLp.contDiff_toLp :
        ContDiff ℝ 1
          (WithLp.toLp 2 : Point3 → H3FourierPoint3))

  have hToLpDiff :
      DifferentiableAt ℝ toLp x := by
    exact
      (hToLpContDiff.differentiable (by norm_num)).differentiableAt

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEq :
      (fun r : ℝ => fderiv ℝ (P r) x)
        =ᶠ[𝓝 s]
      Bop := by
    filter_upwards [hInterval] with r hr

    have hGContDiff :
        ContDiff ℝ 1 (G r) := by
      dsimp only [G, W]
      exact
        h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_one
          hν U₀ hA hU₀ hr.1 hr.2.le i

    have hGDiff :
        DifferentiableAt ℝ (G r) (toLp x) := by
      exact
        (hGContDiff.differentiable (by norm_num)).differentiableAt

    dsimp only [P, G, Bop, Aop, L]

    unfold
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3

    exact
      fderiv_comp
        x
        hGDiff
        hToLpDiff

  exact
    hBop.congr_of_eventuallyEq hEq

end

end Euclidean
end Bridge
end PrimeTensor
