import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityFirstFrechetTimeDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.CubicThirdFrechetTimeContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedForcingGradientTimeContinuity

/-!
# Classicalization: time continuity of the selected first-Fréchet time-derivative candidate

`SelectedVelocityFirstFrechetTimeDerivative` differentiates one fixed spatial
Fréchet-coordinate evaluation of the selected velocity and identifies its
ordinary time derivative with

    ν * Σₖ D³u[eₐ,eₖ,eₖ] - DN[eₐ].

The two ingredients needed to make that coefficient continuous in time are
already available:

* `CubicThirdFrechetTimeContinuity` gives continuity of every fixed evaluated
  third Fréchet derivative of the selected state;
* `SelectedForcingGradientTimeContinuity` gives continuity of the
  operator-valued first Fréchet derivative of the instantaneous forcing.

This file assembles those statements.  The finite third-derivative trace is
handled directly by finite-set induction, and the forcing derivative is
composed with evaluation at the fixed coordinate direction.

No new estimate, limit, or derivative interchange is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityFirstFrechetTimeDerivativeCandidateContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The explicit time-derivative coefficient for one fixed coordinate
Fréchet evaluation of the selected velocity is continuous at every strict
positive interior restart time. -/
theorem h3SelectedVelocity_C1_fderiv_coordinate_timeDerivativeCandidate_continuousAt
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
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    ContinuousAt
      (fun r : ℝ =>
        (ν : ℂ) *
            (∑ k : Fin 3,
              iteratedFDeriv ℝ 3
                (h3SpectralScalarC1Representative
                  (W r i))
                x
                ![
                  ea,
                  h3FourierAxisDirection (h3AxisOfFin3 k),
                  h3FourierAxisDirection (h3AxisOfFin3 k)
                ])
          -
        (fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W r) (W r) i)
            x) ea)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let term : Fin 3 → ℝ → ℂ :=
    fun k r =>
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (W r i))
        x
        ![
          ea,
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  have hTerm
      (k : Fin 3) :
      ContinuousAt (term k) s := by
    dsimp only [term, W, ea]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_thirdFrechet_eval_continuousAt
        hν U₀ hA hU₀ hs hsR i x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 k)
        ]

  have hTrace :
      ContinuousAt
        (fun r : ℝ =>
          ∑ k : Fin 3, term k r)
        s := by
    classical
    change
      Tendsto
        (fun r : ℝ =>
          ∑ k : Fin 3, term k r)
        (𝓝 s)
        (𝓝 (∑ k : Fin 3, term k s))
    exact
      tendsto_finsetSum Finset.univ
        (fun k _ => hTerm k)

  have hViscousTrace :
      ContinuousAt
        (fun r : ℝ =>
          (ν : ℂ) *
            (∑ k : Fin 3, term k r))
        s := by
    exact
      (continuousAt_const :
        ContinuousAt
          (fun _ : ℝ => (ν : ℂ))
          s).mul hTrace

  have hForcingOperator :
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

  have hForcing :
      ContinuousAt
        (fun r : ℝ =>
          (fderiv ℝ
              (h3RawFinLerayOuterProductDivergenceC0Representative
                (W r) (W r) i)
              x) ea)
        s := by
    exact
      ((ContinuousLinearMap.apply ℝ ℂ ea).continuous.continuousAt).comp
        hForcingOperator

  have hCandidate :
      ContinuousAt
        ((fun r : ℝ =>
            (ν : ℂ) *
              (∑ k : Fin 3, term k r)) -
          (fun r : ℝ =>
            (fderiv ℝ
                (h3RawFinLerayOuterProductDivergenceC0Representative
                  (W r) (W r) i)
                x) ea))
        s :=
    hViscousTrace.sub hForcing

  have hPointwise :
      ((fun r : ℝ =>
          (ν : ℂ) *
            (∑ k : Fin 3, term k r)) -
        (fun r : ℝ =>
          (fderiv ℝ
              (h3RawFinLerayOuterProductDivergenceC0Representative
                (W r) (W r) i)
              x) ea))
        =
      (fun r : ℝ =>
        (ν : ℂ) *
            (∑ k : Fin 3, term k r) -
          (fderiv ℝ
              (h3RawFinLerayOuterProductDivergenceC0Representative
                (W r) (W r) i)
              x) ea) := by
    funext r
    rfl

  rw [hPointwise] at hCandidate
  simpa only [term, W, ea] using hCandidate

end

end Euclidean
end Bridge
end PrimeTensor
