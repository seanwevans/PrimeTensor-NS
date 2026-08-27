import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.HessianAssembly
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedSecondCoordinateDuhamelContinuity
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Selected nonlinear Duhamel Hessian field

The endpoint quarter-Hölder branch now supplies all nine mixed coordinate
second derivatives of the complete selected Duhamel reconstruction, and each
mixed derivative is continuous in the spatial point.

This file packages those nine scalar fields into one continuous operator-valued
Hessian candidate

    H3FourierPoint3 →
      H3FourierPoint3 →L[ℝ] (H3FourierPoint3 →L[ℝ] ℂ).

Its values on the canonical axes are definitionally the previously proved
mixed second-coordinate Duhamel derivatives.

The next checkpoint only has to identify this continuous Hessian candidate as
the genuine Fréchet derivative of the already-established first Fréchet
derivative field.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Filter
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterSelectedHessian
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)


/-- Full second-order Duhamel operator assembled from the nine mixed coordinate
second derivatives. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    H3FourierPoint3 →L[ℝ]
      (H3FourierPoint3 →L[ℝ] ℂ) :=
  h3AssembleSecondCoordinateDerivative
    (fun j k : Fin 3 =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
        ν t U V i j k x)

/-- The assembled Hessian candidate recovers every mixed selected coordinate
second derivative on the canonical axes. -/
@[simp]
theorem h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_axis_axis
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t U V i x
        (h3FourierAxisDirection (h3AxisOfFin3 k))
        (h3FourierAxisDirection (h3AxisOfFin3 j))
      =
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
      ν t U V i j k x := by
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
  exact
    h3AssembleSecondCoordinateDerivative_axis_axis
      (fun j k : Fin 3 =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
          ν t U V i j k x)
      j k

/-- Along the selected restart path, the complete assembled Hessian candidate
is continuous in the spatial point. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_selectedRestart_continuous
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Continuous
      (h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3FourierPoint3 → Fin 3 → Fin 3 → ℂ :=
    fun x j k =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
        ν t W W i j k x

  have hD : Continuous D := by
    apply continuous_pi
    intro j
    apply continuous_pi
    intro k
    dsimp only [D]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel_selectedRestart_continuous
        hν U₀ hA hU₀ ht htR i j k

  have hAssembled :
      Continuous
        (fun x : H3FourierPoint3 =>
          h3AssembleSecondCoordinateDerivativeCLM (D x)) :=
    h3AssembleSecondCoordinateDerivativeCLM.continuous.comp hD

  change
    Continuous
      (fun x : H3FourierPoint3 =>
        h3AssembleSecondCoordinateDerivative
          (fun j k : Fin 3 =>
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
              ν t
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀)
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀)
              i j k x))

  simpa only [
    D,
    W,
    h3AssembleSecondCoordinateDerivativeCLM_apply
  ] using hAssembled

end
end Euclidean
end Bridge
end PrimeTensor
