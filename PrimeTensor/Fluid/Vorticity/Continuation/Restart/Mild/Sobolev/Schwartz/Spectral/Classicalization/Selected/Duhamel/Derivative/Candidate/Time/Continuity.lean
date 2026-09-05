import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C0.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.Diagonal.Right.Derivative

/-!
# Classicalization: time continuity of the complete selected Duhamel derivative candidate

`DiagonalRightDerivative` identifies the right derivative of the selected
classical Duhamel diagonal with

    ν * trace(D² Duhamel(t))
      +
    N(W(t), W(t))(x).

The two summands are now separately continuous on every strict positive
interior restart time:

* `SelectedDuhamelHessianTraceTimeContinuity` closes the viscosity-scaled
  Hessian-trace term;
* `SelectedForcingC0TimeContinuity` closes the instantaneous unheated C0
  forcing term.

This file simply packages continuity of their sum.  It introduces no new
estimate or derivative argument.

The resulting function is exactly the derivative candidate occurring in
`h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_hasDerivWithinAt_right`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedDuhamelDerivativeCandidateTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- The complete canonical right-derivative candidate for the selected
classical Duhamel diagonal is continuous at every strict positive interior
restart time. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_derivativeCandidate_continuousAt
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        (ν : ℂ) *
            (∑ j : Fin 3,
              h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
                ν r W W i x
                (h3FourierAxisDirection (h3AxisOfFin3 j))
                (h3FourierAxisDirection (h3AxisOfFin3 j)))
          +
        h3RawFinLerayOuterProductDivergenceC0Representative
          (W r) (W r) i x)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hHessian :
      ContinuousAt
        (fun r : ℝ =>
          (ν : ℂ) *
            (∑ j : Fin 3,
              h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
                ν r W W i x
                (h3FourierAxisDirection (h3AxisOfFin3 j))
                (h3FourierAxisDirection (h3AxisOfFin3 j))))
        s := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_selectedRestart_viscosity_mul_diagonalTrace_continuousAt
        hν U₀ hA hU₀ hs hsR i x

  have hForcing :
      ContinuousAt
        (fun r : ℝ =>
          h3RawFinLerayOuterProductDivergenceC0Representative
            (W r) (W r) i x)
        s := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_diagonal_continuousAt_time
        hν U₀ hA hU₀ hs hsR i x

  exact hHessian.add hForcing

end

end Euclidean
end Bridge
end PrimeTensor
