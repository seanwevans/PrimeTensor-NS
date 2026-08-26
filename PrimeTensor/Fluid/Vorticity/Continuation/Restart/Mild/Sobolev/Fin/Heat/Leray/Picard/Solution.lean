import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Estimate.Data
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Path.Space

/-!
# Concrete Banach-selected spectral heat--Leray mild solution

The analytic work is now packaged in
`h3SpectralFinHeatLerayEstimateData`.  This file performs the final fixed-point
wiring at one physical lifespan `τ` satisfying the standard small-time
condition

    8 C A sqrt(τ) ≤ 1.

It exposes:

* the concrete `RestartPicardProblem` on normalized spectral H³ paths;
* the Banach-selected solution path;
* the actual heat--Leray mild fixed-point equation, stated with the physical
  non-totalized Duhamel path operator;
* the inherited pointwise `2A` bound.

No new PDE estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/--
The concrete small-time hypothesis has exactly the shape required by the
abstract estimate-data package.
-/
theorem h3SpectralFinHeatLerayEstimateData_smallTime
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1) :
    8 *
        (h3SpectralFinHeatLerayEstimateData
          hν hτ U₀ hA hU₀).C *
        (h3SpectralFinHeatLerayEstimateData
          hν hτ U₀ hA hU₀).A *
        Real.sqrt τ
      ≤ 1 := by
  exact hsmall

/--
The invariant contracting Picard problem attached to the concrete finite
heat--Leray estimates at lifespan `τ`.
-/
noncomputable def h3SpectralFinHeatLerayRestartPicardProblem
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1) :
    RestartPicardProblem H3SpectralVelocityPath :=
  (h3SpectralFinHeatLerayEstimateData
      hν hτ U₀ hA hU₀).toRestartPicardProblem
    τ
    hτ
    (h3SpectralFinHeatLerayEstimateData_smallTime
      hν hτ U₀ hA hU₀ hsmall)

/--
The actual spectral H³ mild path selected by Banach's fixed-point theorem.
-/
noncomputable def h3SpectralFinHeatLerayMildSolution
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1) :
    H3SpectralVelocityPath :=
  (h3SpectralFinHeatLerayRestartPicardProblem
    hν hτ U₀ hA hU₀ hsmall).solution

/--
The Banach-selected path satisfies the concrete finite heat--Leray mild
equation on the normalized interval.
-/
theorem h3SpectralFinHeatLerayMildSolution_satisfies_mild
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1) :
    h3SpectralVelocityHeatFreePath ν τ hν.le hτ U₀
        +
      h3SpectralFinHeatLerayDuhamelPathOperator
        hν hτ
        (h3SpectralFinHeatLerayMildSolution
          hν hτ U₀ hA hU₀ hsmall)
        (h3SpectralFinHeatLerayMildSolution
          hν hτ U₀ hA hU₀ hsmall)
      =
    h3SpectralFinHeatLerayMildSolution
      hν hτ U₀ hA hU₀ hsmall := by
  have h :=
    (h3SpectralFinHeatLerayEstimateData
      hν hτ U₀ hA hU₀).solution_satisfies_heatLeray_mild
        τ
        hτ
        (h3SpectralFinHeatLerayEstimateData_smallTime
          hν hτ U₀ hA hU₀ hsmall)
  simpa only [
    h3SpectralFinHeatLerayEstimateData,
    h3SpectralFinHeatLerayDuhamelPathOperatorTotal_of_nonneg hν hτ,
    h3SpectralFinHeatLerayMildSolution,
    h3SpectralFinHeatLerayRestartPicardProblem
  ] using h

/-- Every normalized time slice of the selected mild path has norm at most `2A`. -/
theorem norm_h3SpectralFinHeatLerayMildSolution_apply_le_twoA
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (s : H3UnitTime) :
    ‖h3SpectralFinHeatLerayMildSolution
        hν hτ U₀ hA hU₀ hsmall s‖
      ≤ 2 * A := by
  have h :=
    H3PathHeatLerayEstimateData.solution_pointwise_norm_le_twoA
      (h3SpectralFinHeatLerayEstimateData
        hν hτ U₀ hA hU₀)
      τ
      hτ
      (h3SpectralFinHeatLerayEstimateData_smallTime
        hν hτ U₀ hA hU₀ hsmall)
      s
  simpa only [
    h3SpectralFinHeatLerayEstimateData,
    h3SpectralFinHeatLerayMildSolution,
    h3SpectralFinHeatLerayRestartPicardProblem
  ] using h

end

end Euclidean
end Bridge
end PrimeTensor
