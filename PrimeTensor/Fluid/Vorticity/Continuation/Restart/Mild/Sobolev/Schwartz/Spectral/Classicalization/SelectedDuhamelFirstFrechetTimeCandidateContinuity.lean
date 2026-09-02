import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelThirdFrechetTimeContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedForcingGradientTimeContinuity

/-!
# Classicalization: continuity of the selected Duhamel first-Fréchet time candidate

For the selected Duhamel reconstruction

    D(t,x),

the expected time derivative of one fixed spatial derivative is

    ν * Σₖ D³D(t,x)[eₐ,eₖ,eₖ]
      + D F(W(t),W(t))(x)[eₐ].

The preceding classicalization layers now provide both continuity inputs:

* every ordered coordinate evaluation of `D³D` is time-continuous;
* the complete spatial Fréchet derivative of the instantaneous forcing is
  time-continuous as a continuous-linear-map-valued path.

This file performs only the finite-dimensional assembly: sum the three
diagonal third-jet terms, multiply by the constant viscosity, evaluate the
forcing derivative on the fixed coordinate direction, and add.

No new estimate, temporal derivative, or mixed-partial interchange is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetTimeCandidateContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

attribute [local instance 1100] NormedSpace.complexToReal

/-- The coordinate-evaluated time-derivative candidate for the selected
Duhamel first spatial Fréchet derivative is continuous at every strict
positive interior restart time. -/
theorem h3SelectedDuhamel_firstFrechet_timeDerivativeCandidate_coordinate_continuousAt
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        (ν : ℂ) *
            (∑ k : Fin 3,
              iteratedFDeriv ℝ 3
                (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                  ν r W W i)
                x
                ![
                  h3FourierAxisDirection (h3AxisOfFin3 a),
                  h3FourierAxisDirection (h3AxisOfFin3 k),
                  h3FourierAxisDirection (h3AxisOfFin3 k)
                ])
          +
        (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W r) (W r) i)
          x)
          (h3FourierAxisDirection (h3AxisOfFin3 a)))
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let T : Fin 3 → ℝ → ℂ :=
    fun k r =>
      iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i)
        x
        ![
          ea,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  have hT0 :
      ContinuousAt (T 0) s := by
    dsimp only [T, ea, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_thirdFrechet_coordinate_eval_continuousAt_time
        hν U₀ hA hU₀ hs hsR i a 0 0 x

  have hT1 :
      ContinuousAt (T 1) s := by
    dsimp only [T, ea, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_thirdFrechet_coordinate_eval_continuousAt_time
        hν U₀ hA hU₀ hs hsR i a 1 1 x

  have hT2 :
      ContinuousAt (T 2) s := by
    dsimp only [T, ea, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_thirdFrechet_coordinate_eval_continuousAt_time
        hν U₀ hA hU₀ hs hsR i a 2 2 x

  have hTracePath :
      (fun r : ℝ => ∑ k : Fin 3, T k r)
        =
      T 0 + T 1 + T 2 := by
    funext r
    rw [Fin.sum_univ_three]
    rfl

  have hTrace :
      ContinuousAt
        (fun r : ℝ => ∑ k : Fin 3, T k r)
        s := by
    rw [hTracePath]
    exact (hT0.add hT1).add hT2

  have hNu :
      ContinuousAt
        (fun _ : ℝ => (ν : ℂ))
        s :=
    continuousAt_const

  have hViscosity :
      ContinuousAt
        (fun r : ℝ =>
          (ν : ℂ) * (∑ k : Fin 3, T k r))
        s :=
    hNu.mul hTrace

  have hForceOperator :
      ContinuousAt
        (fun r : ℝ =>
          fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W r) (W r) i)
            x)
        s := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_fderiv_continuousAt_time
        hν U₀ hA hU₀ hs hsR i x

  have hForce :
      ContinuousAt
        (fun r : ℝ =>
          (fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W r) (W r) i)
            x) ea)
        s := by
    exact
      ((ContinuousLinearMap.apply ℝ ℂ ea).continuous.continuousAt).comp
        hForceOperator

  change
    ContinuousAt
      (fun r : ℝ =>
        (ν : ℂ) * (∑ k : Fin 3, T k r)
          +
        (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W r) (W r) i)
          x) ea)
      s

  exact hViscosity.add hForce

end

end Euclidean
end Bridge
end PrimeTensor
