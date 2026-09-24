import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.RHS.Difference.Pressure.Family
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Projected.RHS.Energy.Automatic

/-!
# Ambient selected--old weak energy integrand

The endpoint-independent weak FTC is now uniform over all compact smooth
divergence-free tests.  Before passing to an energy argument, it is convenient
to put the two concrete selected--old Hilbert vectors on the same ambient-real
elapsed-time domain.

This file defines the ambient selected--old velocity difference

    D_real(r)

by zero extension of the existing closed-subtype difference, alongside the
already-defined ambient selected--old projected RHS

    RΔ_real(r).

On every physical elapsed time `r ∈ [0,tau]` these are exactly the concrete
closed-subtype states used by the weak--strong spatial estimates.

Two consequences are packaged:

* for every divergence-free compact weak test, the scalar pairing with
  `RΔ_real` is interval-integrable under the family-level pressure frontier;
* the automatic weak--strong quadratic estimate transports pointwise to the
  ambient representatives:

      2 <D_real(r), RΔ_real(r)>
        ≤ 6 B(E) ‖D_real(r)‖².

This is the scalar energy integrand needed by the forthcoming endpoint-
independent weak energy argument.  No strong old `L²` time derivative or old
endpoint continuity is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyIntegrand
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Ambient-real selected-minus-old velocity difference on `[0,tau]`, extended
by zero outside the physical elapsed interval. -/
noncomputable def h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (r : ℝ) :
    H3PhysicalRealFinVectorL2Hilbert :=
  if hr : r ∈ Set.Icc (0 : ℝ) tau then
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail ⟨r, hr⟩
  else
    0

@[simp]
theorem h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hr : r ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail r
      =
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail ⟨r, hr⟩ := by
  simp only [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed,
    dite_eq_left hr
  ]

/-- Under the family-level pressure frontier, every divergence-free compact
weak test has an interval-integrable pairing with the ambient selected-minus-old
projected RHS. -/
theorem intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifferenceReal_of_allPressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau) :
    IntervalIntegrable
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
            hNS ht hEnd hE hTail htauR r))
      volume
      (0 : ℝ)
      (q : ℝ) := by
  have hSelected :
      IntervalIntegrable
        (fun r : ℝ =>
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
              hNS ht hE hTail htauR r))
        volume
        (0 : ℝ)
        (q : ℝ) :=
    intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSRealOnElapsed
      hNS ht htau hE hTail htauR φ q.property

  have hOld :
      IntervalIntegrable
        (fun r : ℝ =>
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
              hNS ht hEnd hTail r))
        volume
        (0 : ℝ)
        (q : ℝ) :=
    intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal_of_allDivergenceFreePressureDefect
      hNS ht hEnd hE hTail hPressure φ hφ q

  have hSub := hSelected.sub hOld

  simpa only [
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed,
    inner_sub_right
  ] using hSub

/-- The automatic selected--old projected-RHS quadratic estimate, transported
to the ambient-real representatives at one physical elapsed time. -/
theorem two_inner_selectedOldRealProjectedRHSDifference_le_six_mul_norm_sq_of_mem
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
    2 *
      inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r)
      ≤
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2 := by
  rw [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail hr,
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail htauR hr
  ]

  exact
    two_inner_selectedOldUnitProjectedRHSDifference_le_six_mul_norm_sq_alternate_auto
      hNS ht hEnd hE hTail htauR ⟨r, hr⟩

end

end Euclidean
end Bridge
end PrimeTensor
