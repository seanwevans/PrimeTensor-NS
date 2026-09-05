import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Ordinary.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Time.Derivative.Heat.Reduction

/-!
# Classicalization: ordinary time derivative of the selected complex velocity

The selected pointwise mild equation is

    u_i(t,x) = Heat_i(t,x) - Duhamel_i(t,x).

`SelectedVelocityTimeDerivativeHeatReduction` already proves that any ordinary
time derivative of the classical Duhamel diagonal transfers immediately to an
ordinary derivative of the selected C1 representative.

`SelectedDuhamelOrdinaryTimeDerivative` now supplies exactly that missing
ordinary Duhamel derivative.  Therefore this file closes the ordinary
positive-time derivative of every selected complex velocity coordinate at every
strict interior restart time.

No new estimate, FTC argument, or Fourier calculation is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityOrdinaryTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Every selected complex C1 velocity coordinate has an ordinary time
derivative at each strict positive interior restart time.  Its derivative is
the scalar heat generator minus the complete classical Duhamel derivative
candidate. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    HasDerivAt
      (fun s : ℝ =>
        h3SpectralScalarC1Representative (W s i) x)
      (h3SpectralScalarHeatTimeGeneratorRepresentative
          ν t (U₀ i) x
        -
        ((ν : ℂ) *
            (∑ j : Fin 3,
              h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
                ν t W W i x
                (h3FourierAxisDirection (h3AxisOfFin3 j))
                (h3FourierAxisDirection (h3AxisOfFin3 j)))
          +
        h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i x))
      t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let dD : ℂ :=
    (ν : ℂ) *
        (∑ j : Fin 3,
          h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
            ν t W W i x
            (h3FourierAxisDirection (h3AxisOfFin3 j))
            (h3FourierAxisDirection (h3AxisOfFin3 j)))
      +
    h3RawFinLerayOuterProductDivergenceC0Representative
      (W t) (W t) i x

  have hD :
      HasDerivAt
        (fun s : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν s W W i x)
        dD
        t := by
    dsimp only [dD, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_hasDerivAt_time
        hν U₀ hA hU₀ ht htR i x

  have hSelected :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_hasDerivAt_time_of_Duhamel
      hν U₀ hA hU₀ ht htR i x dD
      (by
        simpa only [W] using hD)

  simpa only [W, dD] using hSelected

/-- Equality form of the selected ordinary time derivative. -/
theorem deriv_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    deriv
      (fun s : ℝ =>
        h3SpectralScalarC1Representative (W s i) x)
      t
      =
    h3SpectralScalarHeatTimeGeneratorRepresentative
        ν t (U₀ i) x
      -
    ((ν : ℂ) *
        (∑ j : Fin 3,
          h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
            ν t W W i x
            (h3FourierAxisDirection (h3AxisOfFin3 j))
            (h3FourierAxisDirection (h3AxisOfFin3 j)))
      +
    h3RawFinLerayOuterProductDivergenceC0Representative
      (W t) (W t) i x) := by
  dsimp only

  exact
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_hasDerivAt_time
      hν U₀ hA hU₀ ht htR i x).deriv

end

end Euclidean
end Bridge
end PrimeTensor
