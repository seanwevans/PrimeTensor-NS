import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Deriv.Time.Continuity

/-!
# Classicalization: complex selected temporal derivative regularity on the restart interval

The preceding classicalization files now give, at every strict positive
interior restart-relative time:

* an ordinary `HasDerivAt` theorem for the selected complex C1
  representative;
* `ContinuousAt` for its actual one-dimensional `deriv`.

This file packages those pointwise statements over the whole open relative
restart interval `(0,R)` as exactly

    DifferentiableOn ℝ f (Ioo 0 R)
      ∧
    ContinuousOn (deriv f) (Ioo 0 R).

No new estimate, no new analytic hypothesis, and no new frontier proposition
are introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityComplexTemporalDerivativeRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- On the entire strict relative restart interval, every selected complex C1
velocity coordinate is differentiable in time and its ordinary derivative is
continuous. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_temporalDerivativeRegularity
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let f : ℝ → ℂ :=
      fun s : ℝ =>
        h3SpectralScalarC1Representative (W s i) x
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

  let f : ℝ → ℂ :=
    fun s : ℝ =>
      h3SpectralScalarC1Representative (W s i) x

  let I : Set ℝ :=
    Set.Ioo 0 R

  constructor
  · intro s hs

    have hDeriv :
        HasDerivAt f
          (h3SpectralScalarHeatTimeGeneratorRepresentative
              ν s (U₀ i) x
            -
            ((ν : ℂ) *
                (∑ j : Fin 3,
                  h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
                    ν s W W i x
                    (h3FourierAxisDirection (h3AxisOfFin3 j))
                    (h3FourierAxisDirection (h3AxisOfFin3 j)))
              +
            h3RawFinLerayOuterProductDivergenceC0Representative
              (W s) (W s) i x))
          s := by
      dsimp only [f, W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_hasDerivAt_time
          hν U₀ hA hU₀
          hs.1
          (by
            simpa only [I, R] using hs.2)
          i x

    exact hDeriv.differentiableAt.differentiableWithinAt

  · intro s hs

    have hContinuous :
        ContinuousAt
          (deriv f)
          s := by
      dsimp only [f, W]
      exact
        deriv_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_continuousAt_time
          hν U₀ hA hU₀
          hs.1
          (by
            simpa only [I, R] using hs.2)
          i x

    exact hContinuous.continuousWithinAt

end

end Euclidean
end Bridge
end PrimeTensor
