import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Path.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Difference.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Identification
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureFamilySpan

/-!
# Density access to the selected--old weak energy path

The actual selected--old difference is now known to be strongly continuous.
For the weak energy argument we must also be able to use that difference as the
limit of admissible compact smooth divergence-free test states.

The project has already proved the two exact structural facts needed here:

* every concrete selected--old difference is Leray-fixed;
* the closed real span of compact smooth divergence-free weak tests is exactly
  the physical Leray-fixed Hilbert submodule.

This file combines them.  Every physical difference state `D(q)` lies in the
weak-test closed span, and therefore admits arbitrarily accurate approximation
in the native physical `L²` Hilbert norm by the realization of a single compact
smooth divergence-free weak-test vector.

This is the density interface needed to insert `D(q)` into the endpoint-
independent weak evolution identity by a closure argument.  No new temporal
regularity is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyDensity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every concrete selected--old velocity difference lies in the closed span of
compact smooth divergence-free weak tests. -/
theorem h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_mem_divergenceFreeWeakTestClosedSpan
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
      ∈
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
  rw [
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
  ]

  exact
    (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff
      (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q)).2
      (h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_lerayFixed
        hNS ht hEnd hE hTail htauR q)

/-- Ambient-real form of the same closed-span membership on the physical
elapsed interval. -/
theorem h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_mem_divergenceFreeWeakTestClosedSpan_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hr : r ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail r
      ∈
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
  rw [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail hr
  ]

  exact
    h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_mem_divergenceFreeWeakTestClosedSpan
      hNS ht hEnd hE hTail htauR ⟨r, hr⟩

/-- Every concrete selected--old difference can be approximated arbitrarily
well in physical `L²` by one compact smooth divergence-free weak-test state. -/
theorem exists_divergenceFreeWeakTest_dist_selectedOldUnitVelocityDifference_lt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ
      ∧
      dist
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        < ε := by
  let D : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q

  have hMem :
      D ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
    dsimp only [D]
    exact
      h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_mem_divergenceFreeWeakTestClosedSpan
        hNS ht hEnd hE hTail htauR q

  unfold h3DivergenceFreeWeakTestPhysicalL2ClosedSpan at hMem

  change
    D ∈
      closure
        (h3DivergenceFreeWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)
    at hMem

  rw [Metric.mem_closure_iff] at hMem

  obtain ⟨Φ, hΦ, hDist⟩ :=
    hMem ε hε

  rw [
    h3DivergenceFreeWeakTestPhysicalL2Span_eq_submodule_zeroSpan
  ] at hΦ

  change
    Φ ∈ h3DivergenceFreeWeakTestPhysicalL2Set
  at hΦ

  rcases hΦ with ⟨φ, hφ, rfl⟩

  exact ⟨φ, hφ, hDist⟩

/-- Ambient-real approximation form, convenient for the future partition
argument at a fixed physical elapsed time. -/
theorem exists_divergenceFreeWeakTest_dist_selectedOldVelocityDifferenceReal_lt_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hr : r ∈ Set.Icc (0 : ℝ) tau)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ
      ∧
      dist
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r)
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        < ε := by
  obtain ⟨φ, hφ, hDist⟩ :=
    exists_divergenceFreeWeakTest_dist_selectedOldUnitVelocityDifference_lt
      hNS ht hEnd hE hTail htauR ⟨r, hr⟩ hε

  refine ⟨φ, hφ, ?_⟩

  rw [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail hr
  ]

  exact hDist

end

end Euclidean
end Bridge
end PrimeTensor
