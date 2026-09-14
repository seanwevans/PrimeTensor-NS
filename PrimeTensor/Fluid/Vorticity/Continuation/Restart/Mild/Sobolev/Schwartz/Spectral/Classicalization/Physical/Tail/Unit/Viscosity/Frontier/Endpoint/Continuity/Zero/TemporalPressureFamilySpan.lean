import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureFamily
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Reduction

/-!
# Zeroth-order endpoint continuity: the divergence-free weak-test image is linear

The forthcoming closure argument needs the quantitative Hilbert pairing bound on
the complete algebraic span of compact smooth divergence-free weak tests.

That span introduces no genuinely new vectors before closure: compact smooth
test vectors are closed under addition and real scalar multiplication,
divergence-freeness is linear, and the canonical physical `L²` packaging is
linear.

This file records that bookkeeping explicitly:

* scalar weak-test `L²` packaging respects addition and scalar multiplication;
* the three-component Hilbert packaging respects `0`, addition and scalar
  multiplication;
* embedded divergence-free weak tests form a real submodule;
* the previously defined algebraic span is exactly that submodule.

Thus the estimate from `TemporalPressureFamily` applies to every vector in the
algebraic span through a single divergence-free weak-test representative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroTemporalPressureFamilySpan
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroTemporalPressureFamilySpan :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Linearity of scalar weak-test L² packaging -/

theorem h3WeakTestFunctionPhysicalL2_add_zeroSpan
    (φ ψ : H3WeakTestFunction) :
    h3WeakTestFunctionPhysicalL2 (φ + ψ)
      =
    h3WeakTestFunctionPhysicalL2 φ
      +
    h3WeakTestFunctionPhysicalL2 ψ := by
  apply MeasureTheory.Lp.ext

  have hAdd :=
    h3WeakTestFunctionPhysicalL2_ae (φ + ψ)

  have hφ :=
    h3WeakTestFunctionPhysicalL2_ae φ

  have hψ :=
    h3WeakTestFunctionPhysicalL2_ae ψ

  have hLpAdd :=
    MeasureTheory.Lp.coeFn_add
      (h3WeakTestFunctionPhysicalL2 φ)
      (h3WeakTestFunctionPhysicalL2 ψ)

  filter_upwards [hAdd, hφ, hψ, hLpAdd] with x hxAdd hxφ hxψ hxLpAdd

  calc
    (h3WeakTestFunctionPhysicalL2 (φ + ψ) : Point3 → ℝ) x
        = (φ + ψ) x := hxAdd
    _ = φ x + ψ x := rfl
    _ =
      (h3WeakTestFunctionPhysicalL2 φ : Point3 → ℝ) x
        +
      (h3WeakTestFunctionPhysicalL2 ψ : Point3 → ℝ) x := by
          rw [hxφ, hxψ]
    _ =
      ((h3WeakTestFunctionPhysicalL2 φ
          +
        h3WeakTestFunctionPhysicalL2 ψ : H3ScalarL2) :
          Point3 → ℝ) x := hxLpAdd.symm

theorem h3WeakTestFunctionPhysicalL2_smul_zeroSpan
    (c : ℝ)
    (φ : H3WeakTestFunction) :
    h3WeakTestFunctionPhysicalL2 (c • φ)
      =
    c • h3WeakTestFunctionPhysicalL2 φ := by
  apply MeasureTheory.Lp.ext

  have hSmul :=
    h3WeakTestFunctionPhysicalL2_ae (c • φ)

  have hφ :=
    h3WeakTestFunctionPhysicalL2_ae φ

  have hLpSmul :=
    MeasureTheory.Lp.coeFn_smul
      c
      (h3WeakTestFunctionPhysicalL2 φ)

  filter_upwards [hSmul, hφ, hLpSmul] with x hxSmul hxφ hxLpSmul

  calc
    (h3WeakTestFunctionPhysicalL2 (c • φ) : Point3 → ℝ) x
        = (c • φ) x := hxSmul
    _ = c * φ x := rfl
    _ =
      c *
      (h3WeakTestFunctionPhysicalL2 φ : Point3 → ℝ) x := by
        rw [hxφ]
    _ =
      ((c • h3WeakTestFunctionPhysicalL2 φ : H3ScalarL2) :
          Point3 → ℝ) x := by
        rw [hxLpSmul]
        rfl

theorem h3WeakTestFunctionPhysicalL2_zero_zeroSpan :
    h3WeakTestFunctionPhysicalL2
        (0 : H3WeakTestFunction)
      =
    (0 : H3ScalarL2) := by
  apply MeasureTheory.Lp.ext

  have hZero :=
    h3WeakTestFunctionPhysicalL2_ae
      (0 : H3WeakTestFunction)

  have hLpZero :=
    MeasureTheory.Lp.coeFn_zero
      ℝ
      (2 : ℝ≥0∞)
      (volume : Measure Point3)

  filter_upwards [hZero, hLpZero] with x hxZero hxLpZero

  rw [hxZero, hxLpZero]
  rfl

/-! ## Linearity of vector weak-test Hilbert packaging -/

theorem h3WeakTestVectorPhysicalL2Hilbert_add_zeroSpan
    (φ ψ : H3WeakTestVector) :
    h3WeakTestVectorPhysicalL2Hilbert (φ + ψ)
      =
    h3WeakTestVectorPhysicalL2Hilbert φ
      +
    h3WeakTestVectorPhysicalL2Hilbert ψ := by
  apply PiLp.ext
  intro i

  simp only [
    h3WeakTestVectorPhysicalL2Hilbert,
    PiLp.toLp_apply,
    PiLp.add_apply,
    Pi.add_apply
  ]

  exact
    h3WeakTestFunctionPhysicalL2_add_zeroSpan
      (φ i) (ψ i)

theorem h3WeakTestVectorPhysicalL2Hilbert_smul_zeroSpan
    (c : ℝ)
    (φ : H3WeakTestVector) :
    h3WeakTestVectorPhysicalL2Hilbert (c • φ)
      =
    c • h3WeakTestVectorPhysicalL2Hilbert φ := by
  apply PiLp.ext
  intro i

  simp only [
    h3WeakTestVectorPhysicalL2Hilbert,
    PiLp.toLp_apply,
    PiLp.smul_apply,
    Pi.smul_apply
  ]

  exact
    h3WeakTestFunctionPhysicalL2_smul_zeroSpan
      c (φ i)

theorem h3WeakTestVectorPhysicalL2Hilbert_zero_zeroSpan :
    h3WeakTestVectorPhysicalL2Hilbert
        (0 : H3WeakTestVector)
      =
    (0 : H3PhysicalRealFinVectorL2Hilbert) := by
  apply PiLp.ext
  intro i

  simp only [
    h3WeakTestVectorPhysicalL2Hilbert,
    PiLp.toLp_apply,
    PiLp.zero_apply,
    Pi.zero_apply
  ]

  exact h3WeakTestFunctionPhysicalL2_zero_zeroSpan

/-! ## Divergence-free weak tests are linear -/

theorem H3WeakTestVectorDivergenceFree_zero_zeroSpan :
    H3WeakTestVectorDivergenceFree
      (0 : H3WeakTestVector) := by
  unfold H3WeakTestVectorDivergenceFree
  simp

theorem H3WeakTestVectorDivergenceFree_add_zeroSpan
    {φ ψ : H3WeakTestVector}
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hψ : H3WeakTestVectorDivergenceFree ψ) :
    H3WeakTestVectorDivergenceFree (φ + ψ) := by
  unfold H3WeakTestVectorDivergenceFree at hφ hψ ⊢

  simp_rw [Pi.add_apply, map_add]
  rw [Finset.sum_add_distrib, hφ, hψ]
  simp

theorem H3WeakTestVectorDivergenceFree_smul_zeroSpan
    (c : ℝ)
    {φ : H3WeakTestVector}
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    H3WeakTestVectorDivergenceFree (c • φ) := by
  unfold H3WeakTestVectorDivergenceFree at hφ ⊢

  simp_rw [Pi.smul_apply, map_smul]
  rw [← Finset.smul_sum, hφ]
  simp

/-! ## The embedded divergence-free family is already a submodule -/

/-- Real submodule consisting exactly of physical `L²` states represented by
compact smooth divergence-free weak-test vectors. -/
noncomputable def h3DivergenceFreeWeakTestPhysicalL2Submodule_zeroSpan :
    Submodule ℝ H3PhysicalRealFinVectorL2Hilbert where
  carrier := h3DivergenceFreeWeakTestPhysicalL2Set
  zero_mem' := by
    refine
      ⟨
        (0 : H3WeakTestVector),
        H3WeakTestVectorDivergenceFree_zero_zeroSpan,
        ?_
      ⟩
    exact h3WeakTestVectorPhysicalL2Hilbert_zero_zeroSpan.symm
  add_mem' := by
    intro Φ Ψ hΦ hΨ
    rcases hΦ with ⟨φ, hφ, rfl⟩
    rcases hΨ with ⟨ψ, hψ, rfl⟩

    refine
      ⟨
        φ + ψ,
        H3WeakTestVectorDivergenceFree_add_zeroSpan hφ hψ,
        ?_
      ⟩

    exact
      h3WeakTestVectorPhysicalL2Hilbert_add_zeroSpan
        φ ψ
  smul_mem' := by
    intro c Φ hΦ
    rcases hΦ with ⟨φ, hφ, rfl⟩

    refine
      ⟨
        c • φ,
        H3WeakTestVectorDivergenceFree_smul_zeroSpan c hφ,
        ?_
      ⟩

    exact
      h3WeakTestVectorPhysicalL2Hilbert_smul_zeroSpan
        c φ

@[simp]
theorem mem_h3DivergenceFreeWeakTestPhysicalL2Submodule_zeroSpan_iff
    (Φ : H3PhysicalRealFinVectorL2Hilbert) :
    Φ ∈ h3DivergenceFreeWeakTestPhysicalL2Submodule_zeroSpan
      ↔
    Φ ∈ h3DivergenceFreeWeakTestPhysicalL2Set := by
  rfl

/-- Since the embedded divergence-free weak-test family is already linear, its
algebraic span is exactly that submodule. -/
theorem h3DivergenceFreeWeakTestPhysicalL2Span_eq_submodule_zeroSpan :
    h3DivergenceFreeWeakTestPhysicalL2Span
      =
    h3DivergenceFreeWeakTestPhysicalL2Submodule_zeroSpan := by
  unfold h3DivergenceFreeWeakTestPhysicalL2Span

  apply le_antisymm

  · apply Submodule.span_le.2
    intro Φ hΦ
    exact hΦ

  · intro Φ hΦ
    exact
      Submodule.subset_span
        hΦ

end

end Euclidean
end Bridge
end PrimeTensor
