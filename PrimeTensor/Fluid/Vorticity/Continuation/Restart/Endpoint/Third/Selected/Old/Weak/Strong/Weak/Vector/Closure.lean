import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Leray.Weak.Determining

/-!
# Weak-test closure for the actual selected--old velocity difference

The concrete unit-viscosity selected--old physical `L²` velocity difference

    D(q) = U_sel(q) - U_old(q)

is already Leray-fixed on every closed strict elapsed interval.  The preceding
weak-determining theorem proves that compact smooth divergence-free tests
separate all states in that same Hilbert subspace.

This file combines those two facts into the exact closure interface needed by
the endpoint-independent temporal argument.

If `X` is any Leray-fixed physical `L²` state and

    ⟪Φ, D(q)⟫ = ⟪Φ, X⟫

for every compact smooth divergence-free weak test `Φ`, then

    D(q) = X.

In particular, if all such pairings with `D(q)` vanish, then the physical
difference itself vanishes; at positive elapsed time this upgrades immediately
to pointwise selected/old physical agreement.

The intended next application takes `X` to be the time integral of the
selected-minus-old projected RHS.  No endpoint continuity or strong old
`L²` time derivative is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakVectorClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Divergence-free weak-test pairings determine the concrete selected--old
velocity difference against any Leray-fixed candidate state. -/
theorem h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_eq_of_divergenceFreeWeakTest_pairings_eq
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
    (X : H3PhysicalRealFinVectorL2Hilbert)
    (hX :
      H3PhysicalRealFinVectorL2HilbertLerayFixed X)
    (hPair :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail q)
          =
        inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            X) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
      =
    X := by
  exact
    h3PhysicalRealFinVectorL2Hilbert_eq_of_lerayFixed_of_divergenceFreeWeakTest_pairings_eq
      (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q)
      X
      (h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_lerayFixed
        hNS ht hEnd hE hTail htauR q)
      hX
      hPair

/-- If every divergence-free compact weak test annihilates the selected--old
velocity difference, then the physical `L²` difference itself is zero. -/
theorem h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_eq_zero_of_divergenceFreeWeakTest_pairings
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
    (hPair :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail q)
          =
        0) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
      =
    0 := by
  exact
    h3PhysicalRealFinVectorL2Hilbert_eq_zero_of_lerayFixed_of_divergenceFreeWeakTest_pairing_eq_zero
      (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q)
      (h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_lerayFixed
        hNS ht hEnd hE hTail htauR q)
      hPair

/-- At positive elapsed time, weak annihilation of the actual selected--old
difference upgrades all the way to pointwise equality of the selected smooth
velocity and the old classical velocity. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_divergenceFreeWeakTest_difference_pairings_eq_zero
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
    (hq : 0 < (q : ℝ))
    (hPair :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail q)
          =
        0) :
    H3PreterminalSelectedPhysicalAgreementAt
      (one_pos : (0 : ℝ) < 1)
      (q : ℝ)
      hNS ht hE hTail := by
  have hZero :
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q
        =
      0 :=
    h3PreterminalSelectedOldUnitVelocityPhysicalL2DifferenceOnElapsed_eq_zero_of_divergenceFreeWeakTest_pairings
      hNS ht hEnd hE hTail htauR q hPair

  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2Difference_eq_zero
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q hq
      (q.property.2.trans htauR)
      hZero

end

end Euclidean
end Bridge
end PrimeTensor
