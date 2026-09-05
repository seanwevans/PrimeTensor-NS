import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Schwartz.Dense
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Classicalization: reduce physical Leray density to a trivial annihilator

The preceding checkpoints establish two complementary facts:

* compact smooth divergence-free weak tests lie in the exact physical
  Leray-fixed `L²` submodule;
* unconstrained real Schwartz vector states are dense in the whole physical
  `L²` Hilbert space.

The genuine remaining issue is therefore solenoidal density.

Instead of immediately constructing compactly supported divergence-free
approximants, this file passes to the Hilbert dual formulation.

Write

    K = closed span of compact smooth divergence-free weak tests,
    L = physical Leray-fixed `L²` submodule.

We already know `K ≤ L`.

In a Hilbert space, because `K` is closed,

    L = K ⊔ (Kᗮ ⊓ L).

Hence `K = L` as soon as the relative orthogonal complement

    Kᗮ ⊓ L

is trivial.

Membership in `Kᗮ` implies orthogonality to every original divergence-free
weak-test generator.  Therefore it is enough to prove the concrete uniqueness
statement:

    if V is Leray-fixed and
       ⟪V, φ⟫ = 0
    for every compact smooth divergence-free weak test φ,
    then V = 0.

That is the exact analytic frontier exposed here.

This formulation is designed for the next argument: test against curls of
arbitrary compact smooth vector potentials to obtain distributional curl-free
structure, combine it with Leray-fixed Fourier divergence-free structure, and
deduce that the Fourier transform vanishes almost everywhere.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityDualReduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Concrete annihilator frontier -/

/-- Exact dual uniqueness statement sufficient for the remaining parameter-free
physical Leray density theorem.

A physical `L²` vector in the Leray-fixed subspace must vanish if it is
orthogonal to every compact smooth divergence-free weak-test vector. -/
def H3PhysicalL2LerayFixedDivergenceFreeWeakTestAnnihilatorTrivial : Prop :=
  ∀ V : H3PhysicalRealFinVectorL2Hilbert,
    V ∈ h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule →
    (∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      inner ℝ
          V
          (h3WeakTestVectorPhysicalL2Hilbert φ)
        =
      0) →
    V = 0

/-! ## Generator orthogonality from closed-span orthogonality -/

/-- Every original divergence-free weak-test generator belongs to its defining
closed physical `L²` span. -/
theorem h3WeakTestVectorPhysicalL2Hilbert_mem_divergenceFreeWeakTestClosedSpan
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    h3WeakTestVectorPhysicalL2Hilbert φ
      ∈
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
  apply
    h3DivergenceFreeWeakTestPhysicalL2Span.le_topologicalClosure

  apply Submodule.subset_span

  exact
    ⟨φ, hφ, rfl⟩

/-- A vector orthogonal to the entire closed weak-test span is, in particular,
orthogonal to every original divergence-free weak-test generator. -/
theorem h3Inner_eq_zero_of_mem_divergenceFreeWeakTestClosedSpan_orthogonal
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hV :
      V ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpanᗮ)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    inner ℝ
        V
        (h3WeakTestVectorPhysicalL2Hilbert φ)
      =
    0 := by
  rw [real_inner_comm]

  exact
    hV
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3WeakTestVectorPhysicalL2Hilbert_mem_divergenceFreeWeakTestClosedSpan
        φ hφ)

/-! ## The relative orthogonal complement is trivial -/

/-- The concrete trivial-annihilator statement kills the whole relative
orthogonal complement `Kᗮ ⊓ L`. -/
theorem h3DivergenceFreeWeakTestClosedSpan_orthogonal_inf_lerayFixed_eq_bot_of_annihilatorTrivial
    (hAnnihilator :
      H3PhysicalL2LerayFixedDivergenceFreeWeakTestAnnihilatorTrivial) :
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpanᗮ
        ⊓
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule
      =
    (⊥ : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert) := by
  apply le_antisymm

  · intro V hV

    have hOrth :
        V ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpanᗮ :=
      hV.1

    have hLeray :
        V ∈ h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule :=
      hV.2

    have hGeneratorOrth :
        ∀ φ : H3WeakTestVector,
          H3WeakTestVectorDivergenceFree φ →
          inner ℝ
              V
              (h3WeakTestVectorPhysicalL2Hilbert φ)
            =
          0 := by
      intro φ hφ

      exact
        h3Inner_eq_zero_of_mem_divergenceFreeWeakTestClosedSpan_orthogonal
          hOrth φ hφ

    have hZero :
        V = 0 :=
      hAnnihilator
        V
        hLeray
        hGeneratorOrth

    simpa only [Submodule.mem_bot] using hZero

  · exact bot_le

/-! ## Dual uniqueness implies the full parameter-free density theorem -/

/-- Triviality of the Leray-fixed weak-test annihilator implies that the closed
span of compact smooth divergence-free weak tests is exactly the full physical
Leray-fixed submodule. -/
theorem h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule_of_annihilatorTrivial
    (hAnnihilator :
      H3PhysicalL2LerayFixedDivergenceFreeWeakTestAnnihilatorTrivial) :
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
      =
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  let K :
      Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan

  let L :
      Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule

  have hKL :
      K ≤ L := by
    dsimp only [K, L]

    exact
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_le_lerayFixedSubmodule

  have hInf :
      Kᗮ ⊓ L
        =
      (⊥ : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert) := by
    dsimp only [K, L]

    exact
      h3DivergenceFreeWeakTestClosedSpan_orthogonal_inf_lerayFixed_eq_bot_of_annihilatorTrivial
        hAnnihilator

  have hKClosed :
      IsClosed
        (K : Set H3PhysicalRealFinVectorL2Hilbert) := by
    dsimp only [K]
    unfold h3DivergenceFreeWeakTestPhysicalL2ClosedSpan

    exact
      Submodule.isClosed_topologicalClosure
        h3DivergenceFreeWeakTestPhysicalL2Span

  letI :
      CompleteSpace K :=
    hKClosed.completeSpace_coe

  have hDecomposition :
      K ⊔ (Kᗮ ⊓ L)
        =
      L :=
    Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
      hKL

  have hEq :
      K = L := by
    rw [hInf] at hDecomposition
    simpa only [sup_bot_eq] using hDecomposition

  simpa only [K, L] using hEq

/-- The concrete trivial-annihilator theorem is sufficient for the exact
parameter-free Leray-density frontier introduced earlier. -/
theorem H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_annihilatorTrivial
    (hAnnihilator :
      H3PhysicalL2LerayFixedDivergenceFreeWeakTestAnnihilatorTrivial) :
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan := by
  rw [
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_iff_eq
  ]

  exact
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule_of_annihilatorTrivial
      hAnnihilator

end

end Euclidean
end Bridge
end PrimeTensor
