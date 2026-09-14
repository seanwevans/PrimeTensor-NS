import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalVelocityDifferenceClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Identification
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure

/-!
# Zeroth-order endpoint continuity: strong arbitrary-pair physical L² bound

`TemporalVelocityDifferenceClosure` extends the correct arbitrary elapsed-pair
weak estimate to the complete divergence-free weak-test closed span.

For `r <= q`, define

    V = (U(q) - U(0)) - (U(r) - U(0)).

Each elapsed-zero increment is Leray-fixed, hence so is `V`.  The already proved
identification

    divergence-free weak-test closed span
      =
    physical Leray-fixed submodule

therefore permits `V` itself as a test in the closed-span estimate.

Self-pairing gives

    ‖V‖² <= 3 ‖V‖ C(E) (q-r),

and cancellation of the nonnegative norm factor yields

    ‖V‖ <= 3 C(E) (q-r).

This is the genuine strong two-time physical `L²` modulus needed to close the
zeroth-order Lipschitz frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroTemporalVelocityDifferenceBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Under the all-divergence-free pressure-defect mass frontier, arbitrary
ordered elapsed times satisfy the strong physical `L²` difference bound. -/
theorem norm_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_sub_le_of_allPressureDefect
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
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    ‖h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q
        -
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail r‖
      ≤
    (3 * h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      -
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail r

  have hLeray :
      V ∈
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
    dsimp only [V]

    exact
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule.sub_mem
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_mem_lerayFixedSubmodule
          hNS ht htau hEnd hTail q)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_mem_lerayFixedSubmodule
          hNS ht htau hEnd hTail r)

  have hClosed :
      V ∈
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
    rw [
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
    ]
    exact hLeray

  have hPair :=
    norm_inner_velocityIncrementDifference_le_of_mem_divergenceFreeWeakTestClosedSpan_of_allPressureDefect
      hNS ht htau hEnd hE hTail
      hPressure r q hrq V hClosed

  have hPairSelf :
      ‖inner ℝ V V‖
        ≤
      ((3 * ‖V‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
    change
      ‖inner ℝ
          V
          (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail q
            -
          h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail r)‖
        ≤
      ((3 * ‖V‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ))
    exact hPair

  have hSq :
      ‖V‖ ^ 2
        ≤
      ((3 * ‖V‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
    simpa only [
      real_inner_self_eq_norm_sq,
      Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖V‖)
    ] using hPairSelf

  have hRHSNonneg :
      0 ≤ h3UnitViscosityZeroRHSBound E :=
    h3UnitViscosityZeroRHSBound_nonneg hE

  have hTimeNonneg :
      0 ≤ (q : ℝ) - (r : ℝ) :=
    sub_nonneg.mpr hrq

  have hFinal :
      ‖V‖
        ≤
      (3 * h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
    by_cases hV : ‖V‖ = 0

    · rw [hV]
      exact
        mul_nonneg
          (mul_nonneg (by norm_num) hRHSNonneg)
          hTimeNonneg

    · have hVPos : 0 < ‖V‖ := by
        exact
          lt_of_le_of_ne
            (norm_nonneg V)
            (Ne.symm hV)

      nlinarith [hSq]

  simpa only [V] using hFinal

end

end Euclidean
end Bridge
end PrimeTensor
