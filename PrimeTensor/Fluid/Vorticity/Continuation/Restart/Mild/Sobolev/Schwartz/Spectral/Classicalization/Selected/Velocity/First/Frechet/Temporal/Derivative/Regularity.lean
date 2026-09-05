import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.First.Frechet.Deriv.Time.Continuity

/-!
# Classicalization: first-Fréchet temporal derivative regularity

The selected first spatial Fréchet coordinate is now known, at every strict
positive interior restart time, to have an ordinary time derivative, and that
actual derivative is continuous in time.

This file packages those pointwise statements over the whole open restart
interval `(0,R)` as

    DifferentiableOn ℝ f (Ioo 0 R)
      ∧
    ContinuousOn (deriv f) (Ioo 0 R),

where

    f(r) = D_a u_i(r,x).

This is the first-jet analogue of
`SelectedVelocityComplexTemporalDerivativeRegularity` and is the reusable
complex mixed-regularity package needed before transporting the result to the
real `spatial3.d` formulation used by the continuation glue.

No new estimate, limit, or derivative interchange is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityFirstFrechetTemporalDerivativeRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- On the entire strict restart interval, every fixed coordinate evaluation of
the selected velocity first spatial Fréchet derivative is differentiable in
time and its actual ordinary derivative is continuous. -/
theorem h3SelectedVelocity_C1_fderiv_coordinate_temporalDerivativeRegularity
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let f : ℝ → ℂ :=
      fun r : ℝ =>
        (fderiv ℝ
            (h3SpectralScalarC1Representative
              (W r i))
            x) ea
    let I : Set ℝ :=
      Set.Ioo
        0
        (h3FinHeatLerayRestartRadius ν A)
    DifferentiableOn ℝ f I
      ∧
    ContinuousOn (deriv f) I := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let f : ℝ → ℂ :=
    fun r : ℝ =>
      (fderiv ℝ
          (h3SpectralScalarC1Representative
            (W r i))
          x) ea

  let I : Set ℝ :=
    Set.Ioo 0 R

  constructor

  · intro s hs

    have hDeriv :=
      h3SelectedVelocity_C1_fderiv_coordinate_hasDerivAt_time
        hν U₀ hA hU₀
        hs.1
        (by
          simpa only [I, R] using hs.2)
        i a x

    dsimp only at hDeriv

    have hDifferentiable :
        DifferentiableAt ℝ f s := by
      dsimp only [f, W, ea]
      exact hDeriv.differentiableAt

    exact hDifferentiable.differentiableWithinAt

  · intro s hs

    have hContinuous :
        ContinuousAt
          (deriv f)
          s := by
      dsimp only [f, W, ea]
      exact
        deriv_h3SelectedVelocity_C1_fderiv_coordinate_continuousAt_time
          hν U₀ hA hU₀
          hs.1
          (by
            simpa only [I, R] using hs.2)
          i a x

    exact hContinuous.continuousWithinAt

end

end Euclidean
end Bridge
end PrimeTensor
