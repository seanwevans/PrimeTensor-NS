import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quadratic.Second.Frechet.Time.Continuity

/-!
# Classicalization: time continuity of the selected Hessian trace

`QuadraticSecondFrechetTimeContinuity` proves continuity in time of every fixed
evaluation of the selected complex representative's second spatial Frechet
derivative at every strict positive interior restart time.

The temporal Duhamel derivative candidate uses only the diagonal trace of that
Hessian.  This file packages exactly that finite-dimensional consequence:
evaluate the second Frechet derivative twice in each of the three canonical
Fourier-coordinate directions and sum the three resulting complex scalars.

No new Fourier, heat-kernel, endpoint, or Navier--Stokes estimate appears here.
The proof is only the three already-closed continuity statements plus finite
addition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedHessianTraceTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- At every strict positive interior restart time, the diagonal trace of the
selected complex representative's second spatial Frechet derivative is
continuous in time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_secondFrechet_diagonalTrace_continuousAt
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
        ∑ j : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative (W r i))
            x
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j)))
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hdiag
      (j : Fin 3) :
      ContinuousAt
        (fun r : ℝ =>
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative (W r i))
            x
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j)))
        s := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_secondFrechet_eval_continuousAt
        hν U₀ hA hU₀ hs hsR i x
        (fun _ : Fin 2 =>
          h3FourierAxisDirection (h3AxisOfFin3 j))

  have hsum :
      ContinuousAt
        (fun r : ℝ =>
          iteratedFDeriv ℝ 2
              (h3SpectralScalarC1Representative (W r i))
              x
              (fun _ : Fin 2 =>
                h3FourierAxisDirection
                  (h3AxisOfFin3 (0 : Fin 3)))
            +
          iteratedFDeriv ℝ 2
              (h3SpectralScalarC1Representative (W r i))
              x
              (fun _ : Fin 2 =>
                h3FourierAxisDirection
                  (h3AxisOfFin3 (1 : Fin 3)))
            +
          iteratedFDeriv ℝ 2
              (h3SpectralScalarC1Representative (W r i))
              x
              (fun _ : Fin 2 =>
                h3FourierAxisDirection
                  (h3AxisOfFin3 (2 : Fin 3))))
        s := by
    exact
      ((hdiag (0 : Fin 3)).add
        (hdiag (1 : Fin 3))).add
          (hdiag (2 : Fin 3))

  simpa only [Fin.sum_univ_three] using hsum

end

end Euclidean
end Bridge
end PrimeTensor
