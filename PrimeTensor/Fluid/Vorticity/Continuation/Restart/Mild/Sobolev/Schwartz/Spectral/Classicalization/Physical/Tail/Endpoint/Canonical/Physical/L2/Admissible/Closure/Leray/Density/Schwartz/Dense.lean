import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Test.Fixed
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.NhdsWithin

/-!
# Classicalization: unconstrained physical Schwartz density

The preceding checkpoint proved the easy solenoidal inclusion

    closed span of compact smooth divergence-free tests
      ≤
    physical Leray-fixed L².

The remaining reverse inclusion is a genuine *solenoidal* density problem.
Before modifying approximants to preserve divergence, we isolate the part of
density that Mathlib already supplies for free.

Mathlib proves that real Schwartz functions are dense in scalar `L²`.  This
file transports that theorem through the project's concrete three-component
physical Hilbert product:

    (Fin 3 → 𝓢(Point3, ℝ))
      →
    PiLp 2 (fun _ : Fin 3 => H3ScalarL2).

The coordinatewise map has dense range because:

* `SchwartzMap.denseRange_toLpCLM` gives density in each scalar coordinate;
* `DenseRange.piMap` gives density in the ordinary finite product;
* `WithLp.toLp 2` is a continuous surjection onto the `PiLp 2` carrier.

Consequently the closed real span of arbitrary physical Schwartz vector states
is the whole physical `L²` Hilbert space.

This is deliberately *not* the Leray-density theorem.  No divergence-free
constraint is imposed in this file.  Its purpose is to remove ordinary
smooth/rapid-decay approximation from the analytic frontier.  What remains is
specifically the construction of divergence-free approximants and, later, the
compact-support correction needed to land in the weak-test space.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace SchwartzMap

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensitySchwartzDense
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensitySchwartzDense :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Scalar Schwartz density in the project's physical `L²` carrier -/

/-- Real Schwartz functions on the concrete physical three-space. -/
abbrev H3ScalarSchwartz : Type :=
  𝓢(Point3, ℝ)

/-- Canonical `L²` class of a real Schwartz function. -/
noncomputable def h3ScalarSchwartzPhysicalL2
    (ψ : H3ScalarSchwartz) :
    H3ScalarL2 :=
  (SchwartzMap.toLpCLM
    ℝ
    ℝ
    (2 : ℝ≥0∞)
    (volume : Measure Point3))
    ψ

@[simp]
theorem h3ScalarSchwartzPhysicalL2_apply
    (ψ : H3ScalarSchwartz) :
    h3ScalarSchwartzPhysicalL2 ψ
      =
    (SchwartzMap.toLpCLM
      ℝ
      ℝ
      (2 : ℝ≥0∞)
      (volume : Measure Point3))
      ψ := rfl

/-- Mathlib's Schwartz-density theorem specialized to the project's scalar
physical `L²(Point3)` carrier. -/
theorem denseRange_h3ScalarSchwartzPhysicalL2 :
    DenseRange h3ScalarSchwartzPhysicalL2 := by
  unfold h3ScalarSchwartzPhysicalL2

  exact
    SchwartzMap.denseRange_toLpCLM
      (E := Point3)
      (F := ℝ)
      (p := (2 : ℝ≥0∞))
      (μ := (volume : Measure Point3))
      ENNReal.ofNat_ne_top

/-! ## Coordinatewise finite-vector Schwartz density -/

/-- Three-component real Schwartz vector state in physical space. -/
abbrev H3PhysicalRealFinVectorSchwartz : Type :=
  Fin 3 → H3ScalarSchwartz

/-- Coordinatewise scalar `L²` realization before applying the `PiLp 2`
wrapper.  Writing this map as `Pi.map` lets the product density theorem apply
without any metric estimates. -/
noncomputable def h3PhysicalRealFinVectorSchwartzPhysicalL2Pi :
    H3PhysicalRealFinVectorSchwartz →
      (Fin 3 → H3ScalarL2) :=
  Pi.map
    (fun _ : Fin 3 =>
      h3ScalarSchwartzPhysicalL2)

@[simp]
theorem h3PhysicalRealFinVectorSchwartzPhysicalL2Pi_apply
    (Ψ : H3PhysicalRealFinVectorSchwartz)
    (i : Fin 3) :
    h3PhysicalRealFinVectorSchwartzPhysicalL2Pi Ψ i
      =
    h3ScalarSchwartzPhysicalL2 (Ψ i) := rfl

/-- Coordinatewise scalar Schwartz density gives density in the ordinary
three-component product. -/
theorem denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Pi :
    DenseRange h3PhysicalRealFinVectorSchwartzPhysicalL2Pi := by
  unfold h3PhysicalRealFinVectorSchwartzPhysicalL2Pi

  exact
    DenseRange.piMap
      (fun _ : Fin 3 =>
        denseRange_h3ScalarSchwartzPhysicalL2)

/-! ## Transport density through the genuine `PiLp 2` Hilbert product -/

/-- Physical `PiLp 2` realization of a three-component real Schwartz state. -/
noncomputable def h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert :
    H3PhysicalRealFinVectorSchwartz →
      H3PhysicalRealFinVectorL2Hilbert :=
  (fun V : Fin 3 → H3ScalarL2 =>
      (WithLp.toLp (2 : ℝ≥0∞) V :
        H3PhysicalRealFinVectorL2Hilbert))
    ∘
  h3PhysicalRealFinVectorSchwartzPhysicalL2Pi

@[simp]
theorem h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert_apply
    (Ψ : H3PhysicalRealFinVectorSchwartz) :
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Ψ
      =
    WithLp.toLp
      (2 : ℝ≥0∞)
      (fun i : Fin 3 =>
        h3ScalarSchwartzPhysicalL2 (Ψ i)) := by
  rfl

/-- The coordinatewise physical Schwartz realization has dense range in the
actual finite `PiLp 2` Hilbert product. -/
theorem denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert :
    DenseRange h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert := by
  let toHilbert :
      (Fin 3 → H3ScalarL2) →
        H3PhysicalRealFinVectorL2Hilbert :=
    fun V =>
      WithLp.toLp (2 : ℝ≥0∞) V

  have hToHilbertSurjective :
      Function.Surjective toHilbert := by
    intro V

    refine
      ⟨WithLp.ofLp V, ?_⟩

    exact
      WithLp.toLp_ofLp
        (p := (2 : ℝ≥0∞))
        V

  have hToHilbertDense :
      DenseRange toHilbert :=
    hToHilbertSurjective.denseRange

  have hToHilbertContinuous :
      Continuous toHilbert := by
    exact
      PiLp.continuous_toLp
        (2 : ℝ≥0∞)
        (fun _ : Fin 3 => H3ScalarL2)

  have hComp :
      DenseRange
        (toHilbert ∘
          h3PhysicalRealFinVectorSchwartzPhysicalL2Pi) :=
    hToHilbertDense.comp
      denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Pi
      hToHilbertContinuous

  simpa only [
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert,
    toHilbert
  ] using hComp

/-! ## Closed span of arbitrary Schwartz vectors is all physical `L²` -/

/-- Physical `L²` states represented by arbitrary three-component real
Schwartz functions. -/
noncomputable def h3PhysicalRealFinVectorSchwartzPhysicalL2Set :
    Set H3PhysicalRealFinVectorL2Hilbert :=
  Set.range
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert

/-- Algebraic real span of arbitrary physical Schwartz vector states. -/
noncomputable def h3PhysicalRealFinVectorSchwartzPhysicalL2Span :
    Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
  Submodule.span
    ℝ
    h3PhysicalRealFinVectorSchwartzPhysicalL2Set

/-- Closed real span of arbitrary physical Schwartz vector states. -/
noncomputable def h3PhysicalRealFinVectorSchwartzPhysicalL2ClosedSpan :
    Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
  h3PhysicalRealFinVectorSchwartzPhysicalL2Span.topologicalClosure

/-- Arbitrary real Schwartz vector states already have dense closed span in the
whole physical `L²` Hilbert product. -/
theorem h3PhysicalRealFinVectorSchwartzPhysicalL2ClosedSpan_eq_top :
    h3PhysicalRealFinVectorSchwartzPhysicalL2ClosedSpan
      =
    (⊤ : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert) := by
  apply top_unique

  intro V _hV

  unfold
    h3PhysicalRealFinVectorSchwartzPhysicalL2ClosedSpan

  change
    V ∈
      closure
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)

  have hVRangeClosure :
      V ∈
        closure
          h3PhysicalRealFinVectorSchwartzPhysicalL2Set := by
    unfold h3PhysicalRealFinVectorSchwartzPhysicalL2Set

    exact
      denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert
        V

  exact
    closure_mono
      (by
        intro W hW

        exact
          Submodule.subset_span hW)
      hVRangeClosure

/-- In particular, every physical Leray-fixed `L²` state lies in the closed
span of arbitrary Schwartz vectors.  Thus ordinary smooth density is not the
remaining obstruction; preserving the solenoidal constraint is. -/
theorem h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_le_schwartzPhysicalL2ClosedSpan :
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule
      ≤
    h3PhysicalRealFinVectorSchwartzPhysicalL2ClosedSpan := by
  rw [
    h3PhysicalRealFinVectorSchwartzPhysicalL2ClosedSpan_eq_top
  ]

  exact le_top

end

end Euclidean
end Bridge
end PrimeTensor
