import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Restart.Radius

/-!
# Overlap uniqueness for the finite H³ heat--Leray restart

The canonical restart radius now supplies an actual Banach-selected mild path.
To splice that path to a pre-existing solution, the next requirement is
uniqueness on their common interval.

This file isolates exactly that statement.  First, a fixed point of any
`MildQuadraticPicardData` lying in its invariant ball is equal to the
Banach-selected solution.  We then specialize this to the concrete finite
heat--Leray problem: any normalized spectral path in the `2A` ball satisfying
the same mild equation is the canonical restart path.

The remaining PDE-side overlap theorem therefore only has to show that the
normalized spectral encoding of the old solution

* lies in the `2A` ball, and
* satisfies the same restarted mild equation.

No additional uniqueness argument will be needed there.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

universe u

noncomputable section

/-! ## Abstract uniqueness inside the Picard ball -/

/--
A fixed point of the mild map inside the complete invariant Picard ball is the
Banach-selected solution.
-/
theorem MildQuadraticPicardData.eq_solution_of_mem_domain_of_isFixedPt
    {X : Type u}
    [NormedAddCommGroup X]
    [CompleteSpace X]
    (D : MildQuadraticPicardData X)
    {x : X}
    (hx : x ∈ D.domain)
    (hfix : Function.IsFixedPt D.map x) :
    x = D.toRestartPicardProblem.solution := by
  have hsolmem :
      D.toRestartPicardProblem.solution ∈ D.domain := by
    simpa [MildQuadraticPicardData.toRestartPicardProblem] using
      D.toRestartPicardProblem.solution_mem

  have hsolfix :=
    D.toRestartPicardProblem.solution_isFixedPt
  change
    D.map D.toRestartPicardProblem.solution =
      D.toRestartPicardProblem.solution at hsolfix

  have hdist := D.dist_map_le hx hsolmem
  rw [hfix, hsolfix] at hdist

  have hcontract : (D.contraction : ℝ) < 1 := by
    exact_mod_cast D.contraction_lt_one

  have hnonneg :
      0 ≤ dist x D.toRestartPicardProblem.solution :=
    dist_nonneg

  have hzero :
      dist x D.toRestartPicardProblem.solution = 0 := by
    nlinarith

  exact dist_eq_zero.mp hzero

/-! ## Concrete finite heat--Leray uniqueness -/

/--
At any admissible lifespan, a path in the concrete `2A` Picard ball satisfying
the finite heat--Leray mild equation is the Banach-selected mild path.
-/
theorem h3SpectralFinHeatLerayMildSolution_unique
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (V : H3SpectralVelocityPath)
    (hV : ‖V‖ ≤ 2 * A)
    (hVmild :
      h3SpectralVelocityHeatFreePath ν τ hν.le hτ U₀
          +
        h3SpectralFinHeatLerayDuhamelPathOperator hν hτ V V
        =
      V) :
    V = h3SpectralFinHeatLerayMildSolution
          hν hτ U₀ hA hU₀ hsmall := by
  let E : H3HeatLerayEstimateData H3SpectralVelocityPath :=
    h3SpectralFinHeatLerayEstimateData hν hτ U₀ hA hU₀

  let D : MildQuadraticPicardData H3SpectralVelocityPath :=
    E.toMildQuadraticPicardData τ hτ
      (h3SpectralFinHeatLerayEstimateData_smallTime
        hν hτ U₀ hA hU₀ hsmall)

  have hVmem : V ∈ D.domain := by
    apply (D.mem_domain_iff V).2
    change ‖V‖ ≤ E.radius
    rw [H3HeatLerayEstimateData.radius_eq]
    change ‖V‖ ≤ 2 * A
    exact hV

  have hVfix : Function.IsFixedPt D.map V := by
    change
      h3SpectralVelocityHeatFreePath ν τ hν.le hτ U₀
          +
        h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ V V
        =
      V
    rw [h3SpectralFinHeatLerayDuhamelPathOperatorTotal_of_nonneg hν hτ]
    exact hVmild

  have huniq :=
    D.eq_solution_of_mem_domain_of_isFixedPt hVmem hVfix

  simpa only [
    D,
    E,
    h3SpectralFinHeatLerayMildSolution,
    h3SpectralFinHeatLerayRestartPicardProblem,
    H3HeatLerayEstimateData.toRestartPicardProblem
  ] using huniq

/--
Canonical-radius overlap uniqueness: no small-time hypothesis remains.

Any path in the `2A` ball satisfying the canonical-radius mild equation equals
the canonical restart path.
-/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_unique
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (V : H3SpectralVelocityPath)
    (hV : ‖V‖ ≤ 2 * A)
    (hVmild :
      h3SpectralVelocityHeatFreePath
          ν
          (h3FinHeatLerayRestartRadius ν A)
          hν.le
          (h3FinHeatLerayRestartRadius_pos ν hA).le
          U₀
          +
        h3SpectralFinHeatLerayDuhamelPathOperator
          hν
          (h3FinHeatLerayRestartRadius_pos ν hA).le
          V V
        =
      V) :
    V = h3SpectralFinHeatLerayMildSolutionAtRestartRadius
          hν U₀ hA hU₀ := by
  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadius
  exact
    h3SpectralFinHeatLerayMildSolution_unique
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      V hV hVmild

end

end Euclidean
end Bridge
end PrimeTensor
