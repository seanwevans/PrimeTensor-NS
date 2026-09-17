import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongOldVorticityRawIntegratedCurl
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Closure
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The elementary curl tests are dense in the physical Leray-fixed subspace

The pressure-free vorticity route only produces information for the three
elementary curl-test families

    curl01(ψ), curl02(ψ), curl12(ψ).

To turn those scalar identities into a physical `L²` estimate, we need exactly
the closed-span statement that these three families already generate the
physical Leray-fixed subspace.

The proof is the Hilbert-dual argument already used by the repository for all
divergence-free weak tests:

* every elementary curl test is divergence-free, hence physically Leray-fixed;
* if a Leray-fixed vector is orthogonal to all three curl families, the three
  coordinate expansions say precisely that it is weakly curl-free;
* the proved Helmholtz uniqueness theorem
  `Leray-fixed + weakly curl-free -> 0` kills that relative orthogonal
  complement;
* orthogonal decomposition of a closed submodule then gives equality.

No temporal hypothesis, endpoint continuity, PDE estimate, or density
construction is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongCurlTestDensity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongCurlTestDensity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Physical `L²` states represented by one of the three elementary curl-test
families. -/
noncomputable def h3CurlWeakTestPhysicalL2Set :
    Set H3PhysicalRealFinVectorL2Hilbert :=
  { Φ |
    ∃ ψ : H3WeakTestFunction,
      Φ = h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl01 ψ)
        ∨
      Φ = h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ)
        ∨
      Φ = h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl12 ψ) }

/-- Algebraic real span of the three elementary curl-test families. -/
noncomputable def h3CurlWeakTestPhysicalL2Span :
    Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
  Submodule.span ℝ h3CurlWeakTestPhysicalL2Set

/-- Closed physical Hilbert span of the three elementary curl-test families. -/
noncomputable def h3CurlWeakTestPhysicalL2ClosedSpan :
    Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
  h3CurlWeakTestPhysicalL2Span.topologicalClosure

/-- Every elementary curl-test generator is an unrestricted divergence-free
weak-test state. -/
theorem h3CurlWeakTestPhysicalL2Set_subset_divergenceFreeWeakTestPhysicalL2Set :
    h3CurlWeakTestPhysicalL2Set
      ⊆
    h3DivergenceFreeWeakTestPhysicalL2Set := by
  intro Φ hΦ
  rcases hΦ with ⟨ψ, h01 | h02 | h12⟩

  · subst Φ
    exact
      ⟨
        h3WeakTestCurl01 ψ,
        h3WeakTestCurl01_divergenceFree ψ,
        rfl
      ⟩

  · subst Φ
    exact
      ⟨
        h3WeakTestCurl02 ψ,
        h3WeakTestCurl02_divergenceFree ψ,
        rfl
      ⟩

  · subst Φ
    exact
      ⟨
        h3WeakTestCurl12 ψ,
        h3WeakTestCurl12_divergenceFree ψ,
        rfl
      ⟩

/-- The algebraic curl-test span is contained in the unrestricted
divergence-free weak-test span. -/
theorem h3CurlWeakTestPhysicalL2Span_le_divergenceFreeWeakTestPhysicalL2Span :
    h3CurlWeakTestPhysicalL2Span
      ≤
    h3DivergenceFreeWeakTestPhysicalL2Span := by
  unfold
    h3CurlWeakTestPhysicalL2Span
    h3DivergenceFreeWeakTestPhysicalL2Span

  exact
    Submodule.span_mono
      h3CurlWeakTestPhysicalL2Set_subset_divergenceFreeWeakTestPhysicalL2Set

/-- The closed curl-test span is contained in the physical Leray-fixed
submodule. -/
theorem h3CurlWeakTestPhysicalL2ClosedSpan_le_lerayFixedSubmodule :
    h3CurlWeakTestPhysicalL2ClosedSpan
      ≤
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  have hClosed :
      h3CurlWeakTestPhysicalL2ClosedSpan
        ≤
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
    unfold
      h3CurlWeakTestPhysicalL2ClosedSpan
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan

    exact
      Submodule.topologicalClosure_mono
        h3CurlWeakTestPhysicalL2Span_le_divergenceFreeWeakTestPhysicalL2Span

  exact
    hClosed.trans
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_le_lerayFixedSubmodule

/-- A `curl01` generator belongs to the closed curl-test span. -/
theorem h3WeakTestCurl01PhysicalL2Hilbert_mem_curlWeakTestClosedSpan
    (ψ : H3WeakTestFunction) :
    h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl01 ψ)
      ∈
    h3CurlWeakTestPhysicalL2ClosedSpan := by
  apply
    h3CurlWeakTestPhysicalL2Span.le_topologicalClosure

  apply Submodule.subset_span

  exact
    ⟨ψ, Or.inl rfl⟩

/-- A `curl02` generator belongs to the closed curl-test span. -/
theorem h3WeakTestCurl02PhysicalL2Hilbert_mem_curlWeakTestClosedSpan
    (ψ : H3WeakTestFunction) :
    h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ)
      ∈
    h3CurlWeakTestPhysicalL2ClosedSpan := by
  apply
    h3CurlWeakTestPhysicalL2Span.le_topologicalClosure

  apply Submodule.subset_span

  exact
    ⟨ψ, Or.inr (Or.inl rfl)⟩

/-- A `curl12` generator belongs to the closed curl-test span. -/
theorem h3WeakTestCurl12PhysicalL2Hilbert_mem_curlWeakTestClosedSpan
    (ψ : H3WeakTestFunction) :
    h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl12 ψ)
      ∈
    h3CurlWeakTestPhysicalL2ClosedSpan := by
  apply
    h3CurlWeakTestPhysicalL2Span.le_topologicalClosure

  apply Submodule.subset_span

  exact
    ⟨ψ, Or.inr (Or.inr rfl)⟩

/-- Orthogonality to the closed curl-test span kills the `curl01` pairing. -/
theorem inner_curl01_eq_zero_of_mem_curlWeakTestClosedSpan_orthogonal
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hV : V ∈ h3CurlWeakTestPhysicalL2ClosedSpanᗮ)
    (ψ : H3WeakTestFunction) :
    inner ℝ
        V
        (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl01 ψ))
      =
    0 := by
  rw [real_inner_comm]

  exact
    hV
      (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl01 ψ))
      (h3WeakTestCurl01PhysicalL2Hilbert_mem_curlWeakTestClosedSpan ψ)

/-- Orthogonality to the closed curl-test span kills the `curl02` pairing. -/
theorem inner_curl02_eq_zero_of_mem_curlWeakTestClosedSpan_orthogonal
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hV : V ∈ h3CurlWeakTestPhysicalL2ClosedSpanᗮ)
    (ψ : H3WeakTestFunction) :
    inner ℝ
        V
        (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ))
      =
    0 := by
  rw [real_inner_comm]

  exact
    hV
      (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ))
      (h3WeakTestCurl02PhysicalL2Hilbert_mem_curlWeakTestClosedSpan ψ)

/-- Orthogonality to the closed curl-test span kills the `curl12` pairing. -/
theorem inner_curl12_eq_zero_of_mem_curlWeakTestClosedSpan_orthogonal
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hV : V ∈ h3CurlWeakTestPhysicalL2ClosedSpanᗮ)
    (ψ : H3WeakTestFunction) :
    inner ℝ
        V
        (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl12 ψ))
      =
    0 := by
  rw [real_inner_comm]

  exact
    hV
      (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl12 ψ))
      (h3WeakTestCurl12PhysicalL2Hilbert_mem_curlWeakTestClosedSpan ψ)

/-- A vector orthogonal to the three elementary curl-test families is weakly
curl-free. -/
theorem h3PhysicalRealFinVectorL2Hilbert_weakCurlFree_of_mem_curlWeakTestClosedSpan_orthogonal
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hV : V ∈ h3CurlWeakTestPhysicalL2ClosedSpanᗮ) :
    H3PhysicalRealFinVectorL2HilbertWeakCurlFree V := by
  intro ψ

  have h01 :=
    inner_curl01_eq_zero_of_mem_curlWeakTestClosedSpan_orthogonal
      hV ψ

  have h02 :=
    inner_curl02_eq_zero_of_mem_curlWeakTestClosedSpan_orthogonal
      hV ψ

  have h12 :=
    inner_curl12_eq_zero_of_mem_curlWeakTestClosedSpan_orthogonal
      hV ψ

  rw [
    inner_h3PhysicalRealFinVectorL2Hilbert_weakTestVector,
    Fin.sum_univ_three
  ] at h01 h02 h12

  have h01' :
      inner ℝ
          (V 0)
          (h3WeakTestFunctionPhysicalL2
            (h3WeakTestFunctionSpatialDerivative
              (h3AxisOfFin3 1) ψ))
        -
      inner ℝ
          (V 1)
          (h3WeakTestFunctionPhysicalL2
            (h3WeakTestFunctionSpatialDerivative
              (h3AxisOfFin3 0) ψ))
        =
      0 := by
    simpa only [
      h3WeakTestCurl01_apply_zero,
      h3WeakTestCurl01_apply_one,
      h3WeakTestCurl01_apply_two,
      h3WeakTestFunctionPhysicalL2_neg,
      h3WeakTestFunctionPhysicalL2_zero,
      inner_neg_right,
      inner_zero_right,
      add_zero,
      sub_eq_add_neg
    ] using h01

  have h02' :
      inner ℝ
          (V 0)
          (h3WeakTestFunctionPhysicalL2
            (h3WeakTestFunctionSpatialDerivative
              (h3AxisOfFin3 2) ψ))
        -
      inner ℝ
          (V 2)
          (h3WeakTestFunctionPhysicalL2
            (h3WeakTestFunctionSpatialDerivative
              (h3AxisOfFin3 0) ψ))
        =
      0 := by
    simpa only [
      h3WeakTestCurl02_apply_zero,
      h3WeakTestCurl02_apply_one,
      h3WeakTestCurl02_apply_two,
      h3WeakTestFunctionPhysicalL2_neg,
      h3WeakTestFunctionPhysicalL2_zero,
      inner_neg_right,
      inner_zero_right,
      zero_add,
      add_zero,
      sub_eq_add_neg
    ] using h02

  have h12' :
      inner ℝ
          (V 1)
          (h3WeakTestFunctionPhysicalL2
            (h3WeakTestFunctionSpatialDerivative
              (h3AxisOfFin3 2) ψ))
        -
      inner ℝ
          (V 2)
          (h3WeakTestFunctionPhysicalL2
            (h3WeakTestFunctionSpatialDerivative
              (h3AxisOfFin3 1) ψ))
        =
      0 := by
    simpa only [
      h3WeakTestCurl12_apply_zero,
      h3WeakTestCurl12_apply_one,
      h3WeakTestCurl12_apply_two,
      h3WeakTestFunctionPhysicalL2_neg,
      h3WeakTestFunctionPhysicalL2_zero,
      inner_neg_right,
      inner_zero_right,
      zero_add,
      add_zero,
      sub_eq_add_neg
    ] using h12

  exact ⟨h01', h02', h12'⟩

/-- The relative orthogonal complement of the curl-test closed span inside the
physical Leray-fixed submodule is trivial. -/
theorem h3CurlWeakTestClosedSpan_orthogonal_inf_lerayFixed_eq_bot :
    h3CurlWeakTestPhysicalL2ClosedSpanᗮ
        ⊓
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule
      =
    (⊥ : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert) := by
  apply le_antisymm

  · intro V hV

    have hOrth :
        V ∈ h3CurlWeakTestPhysicalL2ClosedSpanᗮ :=
      hV.1

    have hLeray :
        V ∈ h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule :=
      hV.2

    have hCurl :
        H3PhysicalRealFinVectorL2HilbertWeakCurlFree V :=
      h3PhysicalRealFinVectorL2Hilbert_weakCurlFree_of_mem_curlWeakTestClosedSpan_orthogonal
        hOrth

    have hZero :
        V = 0 :=
      H3PhysicalL2LerayFixedWeakCurlFreeTrivial_proved
        V hLeray hCurl

    simpa only [Submodule.mem_bot] using hZero

  · exact bot_le

/-- The closed span of the three elementary curl-test families is exactly the
physical Leray-fixed submodule. -/
theorem h3CurlWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule :
    h3CurlWeakTestPhysicalL2ClosedSpan
      =
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  let K :
      Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
    h3CurlWeakTestPhysicalL2ClosedSpan

  let L :
      Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule

  have hKL :
      K ≤ L := by
    dsimp only [K, L]
    exact
      h3CurlWeakTestPhysicalL2ClosedSpan_le_lerayFixedSubmodule

  have hInf :
      Kᗮ ⊓ L
        =
      (⊥ : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert) := by
    dsimp only [K, L]
    exact
      h3CurlWeakTestClosedSpan_orthogonal_inf_lerayFixed_eq_bot

  have hKClosed :
      IsClosed
        (K : Set H3PhysicalRealFinVectorL2Hilbert) := by
    dsimp only [K]
    unfold h3CurlWeakTestPhysicalL2ClosedSpan

    exact
      Submodule.isClosed_topologicalClosure
        h3CurlWeakTestPhysicalL2Span

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

end

end Euclidean
end Bridge
end PrimeTensor
