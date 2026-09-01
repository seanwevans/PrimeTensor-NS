import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityOrdinaryTimeDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelDerivativeCandidateTimeContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.GeneratorContinuity

/-!
# Classicalization: continuity of the selected velocity time-derivative candidate

`SelectedVelocityOrdinaryTimeDerivative` identifies the ordinary time
derivative of the selected complex C1 representative with

    heatGenerator(t)
      -
    duhamelDerivativeCandidate(t).

Both summands are already continuous at every strict positive interior restart
time:

* `Heat.Time.GeneratorContinuity` handles the positive-time heat generator;
* `SelectedDuhamelDerivativeCandidateTimeContinuity` handles the complete
  Duhamel derivative candidate.

This file packages continuity of their difference.  It introduces no new
estimate and no new frontier proposition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityDerivativeCandidateTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The explicit ordinary time-derivative candidate for the selected complex
C1 representative is continuous at every strict positive interior restart
time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_timeDerivativeCandidate_continuousAt
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
        h3SpectralScalarHeatTimeGeneratorRepresentative
            ν r (U₀ i) x
          -
        ((ν : ℂ) *
            (∑ j : Fin 3,
              h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
                ν r W W i x
                (h3FourierAxisDirection (h3AxisOfFin3 j))
                (h3FourierAxisDirection (h3AxisOfFin3 j)))
          +
        h3RawFinLerayOuterProductDivergenceC0Representative
          (W r) (W r) i x))
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hHeat :
      ContinuousAt
        (fun r : ℝ =>
          h3SpectralScalarHeatTimeGeneratorRepresentative
            ν r (U₀ i) x)
        s :=
    h3SpectralScalarHeatTimeGeneratorRepresentative_continuousAt_time
      hν hs (U₀ i) x

  have hDuhamel :
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
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_derivativeCandidate_continuousAt
        hν U₀ hA hU₀ hs hsR i x

  exact hHeat.sub hDuhamel

end

end Euclidean
end Bridge
end PrimeTensor
