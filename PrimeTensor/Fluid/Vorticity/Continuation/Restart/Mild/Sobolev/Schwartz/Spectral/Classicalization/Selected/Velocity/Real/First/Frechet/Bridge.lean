import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.First.Frechet.Temporal.Derivative.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Hessian.Trace.Bridge

/-!
# Classicalization: selected real Point3 first-Fréchet bridge

The selected first spatial Fréchet coordinate now has a complete temporal
regularity package on the complex Fourier carrier.  Before transporting that
time derivative to the project's concrete `spatial3.d` language, we isolate
the order-one representation identity.

The real physical representative is obtained by

* taking `Complex.reCLM` on the left, and
* precomposing with the canonical `h3Point3ToFourierCLM` spatial map.

Consequently its first Fréchet derivative is exactly the real part of the
complex first Fréchet derivative after transporting the base point and the
single direction.  The coordinate specialization then uses the already proved
definitional identity

    h3Point3ToFourierCLM (axisDirection a) = h3FourierAxisDirection a.

No new estimate, time derivative, or mixed-partial commutation is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealFirstFrechetBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, the first Fréchet
derivative of the real `Point3` representative is exactly the real part of the
first Fréchet derivative of the complex representative after transporting the
base point and direction through the canonical `Point3 → H3FourierPoint3`
linear map. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_firstFrechet_eval_eq_re
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (m : Fin 1 → Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 1
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W t i))
        x m
      =
    (iteratedFDeriv ℝ 1
        (h3SpectralScalarC1Representative
          (W t i))
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))).re := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hComplexC1 :
      ContDiff ℝ 1
        (h3SpectralScalarC1Representative
          (W t i)) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
        1 hν U₀ hA hU₀ ht htR.le i

  have hRealC1 :
      ContDiff ℝ 1
        (h3SpectralScalarRealC1Representative
          (W t i)) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1Representative_contDiff_nat
        1 hν U₀ hA hU₀ ht htR.le i

  have hLeft :
      iteratedFDeriv ℝ 1
          (h3SpectralScalarRealC1Representative
            (W t i))
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 1
          (h3SpectralScalarC1Representative
            (W t i))
          (h3Point3ToFourierCLM x)) := by
    unfold h3SpectralScalarRealC1Representative

    change
      iteratedFDeriv ℝ 1
          (Complex.reCLM ∘
            h3SpectralScalarC1Representative
              (W t i))
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 1
          (h3SpectralScalarC1Representative
            (W t i))
          (h3Point3ToFourierCLM x))

    exact
      Complex.reCLM.iteratedFDeriv_comp_left
        hComplexC1.contDiffAt
        (by norm_num)

  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_eq_comp
      (W t i)
  ]

  have hRight :=
    h3Point3ToFourierCLM.iteratedFDeriv_comp_right
      hRealC1
      x
      (i := 1)
      (by norm_num)

  rw [hRight]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply
  ]

  rw [hLeft]

  rfl

/-- Coordinate specialization of the first-Fréchet transport theorem.  The
ordinary `Point3` coordinate direction is sent to exactly the Fourier-side
direction used by the selected first-Fréchet temporal regularity theorem. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_firstFrechet_axisDirection_eq_re
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 1
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W t i))
        x
        (fun _ : Fin 1 => axisDirection a)
      =
    (iteratedFDeriv ℝ 1
        (h3SpectralScalarC1Representative
          (W t i))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        (fun _ : Fin 1 => h3FourierAxisDirection a)).re := by
  dsimp only

  have hAxis :
      (WithLp.toLp 2 : Point3 → H3FourierPoint3)
          (axisDirection a)
        =
      h3FourierAxisDirection a := by
    rfl

  simpa only [
    h3Point3ToFourierCLM_apply,
    hAxis
  ] using
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_firstFrechet_eval_eq_re
      hν U₀ hA hU₀ ht htR i x
      (fun _ : Fin 1 => axisDirection a))

end

end Euclidean
end Bridge
end PrimeTensor
