import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C1.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Hessian.Trace.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Ordinary.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Hessian.Trace.Representative

/-!
# Classicalization: selected velocity time derivative in spatial PDE form

The ordinary selected complex time derivative has already been identified as

    heatGenerator
      - (ν * DuhamelHessianTrace + instantaneousForcing).

The twice-spatially differentiated mild identity identifies the Duhamel
Hessian trace with

    heatHessianTrace - selectedHessianTrace,

while the positive-time heat equation identifies the heat generator with
`ν * heatHessianTrace`.

Substitution therefore cancels the heat trace exactly and gives

    ∂ₜ selected
      = ν * selectedHessianTrace - instantaneousForcing.

This is the spatial PDE form needed for the mixed-regularity closure.  The
preceding increment upgrades the instantaneous forcing to spatial `C¹`, while
the selected velocity is already spatial `C³`; the next step can therefore
differentiate this entire temporal derivative once in space.

No new estimate or analytic hypothesis is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityTimeDerivativePDEForm
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The explicit selected complex time-derivative candidate is viscosity times
the selected spatial Hessian trace minus the instantaneous unheated forcing. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_timeDerivativeCandidate_eq_selectedHessianTrace_sub_forcing
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
      (W t) (W t) i x)
      =
    (ν : ℂ) *
        (∑ j : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (W t i))
            x
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j)))
      -
    h3RawFinLerayOuterProductDivergenceC0Representative
      (W t) (W t) i x := by
  dsimp only

  have hHeat :=
    h3SpectralScalarHeatTimeGeneratorRepresentative_eq_viscosity_mul_hessianTrace
      hν ht (U₀ i) x

  have hDuhamel :=
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_selectedRestart_diagonalTrace_eq_heat_sub_selected
      hν U₀ hA hU₀ ht htR.le i x

  dsimp only at hDuhamel

  rw [hHeat, hDuhamel]
  ring

/-- Equality form for the actual one-dimensional derivative of the selected
complex C1 representative.  The heat contribution has disappeared completely:
the derivative is exactly viscosity times the selected spatial Hessian trace
minus the instantaneous forcing. -/
theorem deriv_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_eq_selectedHessianTrace_sub_forcing
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
        h3SpectralScalarC1Representative
          (W s i) x)
      t
      =
    (ν : ℂ) *
        (∑ j : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (W t i))
            x
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j)))
      -
    h3RawFinLerayOuterProductDivergenceC0Representative
      (W t) (W t) i x := by
  dsimp only

  have hDeriv :=
    deriv_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative
      hν U₀ hA hU₀ ht htR i x

  have hPDE :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_timeDerivativeCandidate_eq_selectedHessianTrace_sub_forcing
      hν U₀ hA hU₀ ht htR i x

  dsimp only at hDeriv hPDE

  exact hDeriv.trans hPDE

end

end Euclidean
end Bridge
end PrimeTensor
