import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureFamilySpan

/-!
# Zeroth-order endpoint continuity: extend the weak bound to the closed span

`TemporalPressureFamilySpan` shows that the algebraic span of embedded compact
smooth divergence-free weak tests is already exactly their image submodule.

Under the family-level pressure-defect mass frontier, every vector in that
algebraic span satisfies the quantitative Hilbert pairing estimate against the
old physical velocity increment.

The set

    {Phi | ‖<Phi,V>‖ <= ((3 * ‖Phi‖) * C(E)) * q}

is closed because both sides are continuous functions of `Phi`.  Therefore the
same estimate holds on the topological closure of the divergence-free weak-test
span.

This is the exact topological extension needed before inserting the Leray-fixed
velocity increment itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroTemporalPressureFamilyClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Under the all-divergence-free pressure-defect mass frontier, the quantitative
weak velocity-increment estimate extends from compact smooth divergence-free
tests to their complete physical `L²` closed span. -/
theorem norm_inner_velocityIncrementTo_le_of_mem_divergenceFreeWeakTestClosedSpan_of_allPressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (Φ : H3PhysicalRealFinVectorL2Hilbert)
    (hΦ :
      Φ ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpan) :
    ‖inner ℝ
        Φ
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)‖
      ≤
    ((3 * ‖Φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    (q : ℝ) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
      hNS ht htau hEnd hTail q

  let S : Set H3PhysicalRealFinVectorL2Hilbert :=
    { Ψ |
      ‖inner ℝ Ψ V‖
        ≤
      ((3 * ‖Ψ‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      (q : ℝ) }

  have hClosed : IsClosed S := by
    dsimp only [S]

    exact
      isClosed_le
        ((continuous_id.inner continuous_const).norm)
        (((continuous_const.mul continuous_norm).mul continuous_const).mul
          continuous_const)

  have hSpanSubset :
      (h3DivergenceFreeWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)
        ⊆
      S := by
    intro Ψ hΨ

    rw [
      h3DivergenceFreeWeakTestPhysicalL2Span_eq_submodule_zeroSpan
    ] at hΨ

    change
      Ψ ∈ h3DivergenceFreeWeakTestPhysicalL2Set
    at hΨ

    rcases hΨ with ⟨φ, hφ, rfl⟩

    dsimp only [S, V]

    exact
      norm_inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_le_of_allDivergenceFreePressureDefect
        hNS ht htau hEnd hE hTail
        hPressure φ hφ q

  have hClosureSubset :
      closure
          (h3DivergenceFreeWeakTestPhysicalL2Span :
            Set H3PhysicalRealFinVectorL2Hilbert)
        ⊆
      S :=
    closure_minimal hSpanSubset hClosed

  have hΦClosure :
      Φ ∈
      closure
        (h3DivergenceFreeWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert) := by
    unfold h3DivergenceFreeWeakTestPhysicalL2ClosedSpan at hΦ
    change
      Φ ∈
      closure
        (h3DivergenceFreeWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)
    at hΦ
    exact hΦ

  have hResult := hClosureSubset hΦClosure

  dsimp only [S, V] at hResult
  exact hResult

end

end Euclidean
end Bridge
end PrimeTensor
