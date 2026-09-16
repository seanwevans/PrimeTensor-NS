import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongRHSDifferenceLerayFixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Identification

/-!
# Divergence-free weak tests determine Leray-fixed physical L² states

The endpoint-independent selected--old projected RHS difference is now known to
live in the exact physical Leray-fixed Hilbert subspace.

The repository has independently proved the parameter-free density identity

    closure(span(compact smooth divergence-free weak tests))
      =
    physical Leray-fixed L².

This file packages the dual consequence needed by the weak--strong temporal
argument:

* a Leray-fixed physical `L²` state whose pairing with every divergence-free
  weak test vanishes is zero;
* two Leray-fixed states with identical divergence-free weak-test pairings are
  equal;
* in particular, the endpoint-independent selected--old projected RHS
  difference is determined completely by those weak pairings.

This is the exact Hilbert-space nondegeneracy bridge needed to upgrade future
weak FTC identities into genuine vector identities.  No endpoint continuity,
strong old time derivative, or new density argument is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongLerayWeakDetermining
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A physical Leray-fixed `L²` state is zero if every compact smooth
divergence-free weak test annihilates it. -/
theorem h3PhysicalRealFinVectorL2Hilbert_eq_zero_of_lerayFixed_of_divergenceFreeWeakTest_pairing_eq_zero
    (V : H3PhysicalRealFinVectorL2Hilbert)
    (hFixed :
      H3PhysicalRealFinVectorL2HilbertLerayFixed V)
    (hPair :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            V
          =
        0) :
    V = 0 := by
  let S : Set H3PhysicalRealFinVectorL2Hilbert :=
    h3DivergenceFreeWeakTestPhysicalL2Set

  let K : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
    Submodule.span ℝ S

  let L : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] ℝ :=
    innerSL ℝ V

  have hGeneratorKer :
      S ⊆ L.ker := by
    intro Φ hΦ
    rcases hΦ with ⟨φ, hDiv, rfl⟩

    have hPair0 :
        inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            V
          =
        0 :=
      hPair φ hDiv

    change L (h3WeakTestVectorPhysicalL2Hilbert φ) = 0
    dsimp only [L]

    simpa only [innerSL_apply_apply, real_inner_comm] using hPair0

  have hSpanKer :
      K ≤ L.ker := by
    dsimp only [K]
    exact Submodule.span_le.mpr hGeneratorKer

  have hOrth :
      V ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']
    intro Φ hΦ

    have hKer :
        Φ ∈ L.ker :=
      hSpanKer hΦ

    change L Φ = 0 at hKer
    dsimp only [L] at hKer

    simpa only [innerSL_apply_apply] using hKer

  have hFixedSubmodule :
      V ∈ h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule :=
    (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff V).2
      hFixed

  have hMemClosed :
      V ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
    rw [
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
    ]
    exact hFixedSubmodule

  have hClosedEq :
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
        =
      Kᗮᗮ := by
    dsimp only [K]
    unfold h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
    symm

    exact
      Submodule.orthogonal_orthogonal_eq_closure
        h3DivergenceFreeWeakTestPhysicalL2Span

  have hDouble :
      V ∈ Kᗮᗮ := by
    rw [← hClosedEq]
    exact hMemClosed

  have hBoth :
      V ∈ Kᗮ ⊓ Kᗮᗮ :=
    ⟨hOrth, hDouble⟩

  have hBot :
      V ∈ (⊥ : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert) := by
    rw [← Submodule.inf_orthogonal_eq_bot Kᗮ]
    exact hBoth

  simpa using hBot

/-- Divergence-free compact weak-test pairings separate any two physical
Leray-fixed `L²` states. -/
theorem h3PhysicalRealFinVectorL2Hilbert_eq_of_lerayFixed_of_divergenceFreeWeakTest_pairings_eq
    (V W : H3PhysicalRealFinVectorL2Hilbert)
    (hV :
      H3PhysicalRealFinVectorL2HilbertLerayFixed V)
    (hW :
      H3PhysicalRealFinVectorL2HilbertLerayFixed W)
    (hPair :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            V
          =
        inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            W) :
    V = W := by
  apply sub_eq_zero.mp

  apply
    h3PhysicalRealFinVectorL2Hilbert_eq_zero_of_lerayFixed_of_divergenceFreeWeakTest_pairing_eq_zero
      (V - W)
      (H3PhysicalRealFinVectorL2HilbertLerayFixed.sub hV hW)

  intro φ hφ

  rw [inner_sub_right, hPair φ hφ, sub_self]

/-- The endpoint-independent selected--old projected RHS difference vanishes
whenever every divergence-free compact weak test sees zero pairing. -/
theorem h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed_eq_zero_of_divergenceFreeWeakTest_pairings
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
            (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
              hNS ht hEnd hE hTail htauR q)
          =
        0) :
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q
      =
    0 := by
  exact
    h3PhysicalRealFinVectorL2Hilbert_eq_zero_of_lerayFixed_of_divergenceFreeWeakTest_pairing_eq_zero
      (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q)
      (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed_lerayFixed
        hNS ht hEnd hE hTail htauR q)
      hPair

end

end Euclidean
end Bridge
end PrimeTensor
