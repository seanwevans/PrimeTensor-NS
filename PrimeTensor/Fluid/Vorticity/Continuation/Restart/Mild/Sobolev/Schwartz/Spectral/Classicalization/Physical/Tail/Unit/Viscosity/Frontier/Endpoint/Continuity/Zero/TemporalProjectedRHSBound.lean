import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalProjectedRHSFTC

/-!
# Zeroth-order endpoint continuity: quantitative weak projected-RHS bound

`TemporalProjectedRHSFTC` removes pressure from the final weak evolution
integrand.  The remaining integrand is the finite sum of three genuine real
`L²` Hilbert pairings against the endpoint-independent physical projected RHS.

Each RHS coordinate already satisfies the uniform bound

    ‖R_i(q)‖₂ ≤ h3UnitViscosityZeroRHSBound E.

This file applies Hilbert-space Cauchy--Schwarz coordinatewise and the finite
triangle inequality to obtain one scalar pointwise majorant for the complete
weak RHS pairing.

No temporal integration is performed here.  The next checkpoint can integrate
this constant bound over `[0,q]`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroProjectedRHSWeakPairingBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Coordinate-summed physical `L²` size of one compact weak-test vector. -/
noncomputable def h3WeakTestVectorPhysicalL2L1Norm
    (φ : H3WeakTestVector) :
    ℝ :=
  ∑ i : Fin 3,
    ‖h3WeakTestFunctionPhysicalL2 (φ i)‖

theorem h3WeakTestVectorPhysicalL2L1Norm_nonneg
    (φ : H3WeakTestVector) :
    0 ≤ h3WeakTestVectorPhysicalL2L1Norm φ := by
  unfold h3WeakTestVectorPhysicalL2L1Norm
  exact
    Finset.sum_nonneg
      (fun i hi =>
        norm_nonneg
          (h3WeakTestFunctionPhysicalL2 (φ i)))

/-- The complete endpoint-independent physical projected-RHS weak pairing is
pointwise bounded by the coordinate-summed weak-test `L²` norm times the
uniform unit-viscosity RHS ceiling. -/
theorem norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
        hNS ht hEnd hTail φ q‖
      ≤
    h3WeakTestVectorPhysicalL2L1Norm φ
      *
    h3UnitViscosityZeroRHSBound E := by
  unfold
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed

  calc
    ‖∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
          hNS ht hEnd hTail q i)‖
        ≤
      ∑ i : Fin 3,
        ‖inner ℝ
          (h3WeakTestFunctionPhysicalL2 (φ i))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
            hNS ht hEnd hTail q i)‖ := by
      exact
        norm_sum_le
          (Finset.univ : Finset (Fin 3))
          (fun i : Fin 3 =>
            inner ℝ
              (h3WeakTestFunctionPhysicalL2 (φ i))
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
                hNS ht hEnd hTail q i))
    _ ≤
      ∑ i : Fin 3,
        ‖h3WeakTestFunctionPhysicalL2 (φ i)‖
          *
        h3UnitViscosityZeroRHSBound E := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖inner ℝ
            (h3WeakTestFunctionPhysicalL2 (φ i))
            (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
              hNS ht hEnd hTail q i)‖
            ≤
          ‖h3WeakTestFunctionPhysicalL2 (φ i)‖
            *
          ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
            hNS ht hEnd hTail q i‖ := by
          exact
            norm_inner_le_norm
              (h3WeakTestFunctionPhysicalL2 (φ i))
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
                hNS ht hEnd hTail q i)
        _ ≤
          ‖h3WeakTestFunctionPhysicalL2 (φ i)‖
            *
          h3UnitViscosityZeroRHSBound E := by
          exact
            mul_le_mul_of_nonneg_left
              (norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_le
                hNS ht hEnd hE hTail q i)
              (norm_nonneg
                (h3WeakTestFunctionPhysicalL2 (φ i)))
    _ =
      (∑ i : Fin 3,
        ‖h3WeakTestFunctionPhysicalL2 (φ i)‖)
        *
      h3UnitViscosityZeroRHSBound E := by
      rw [Finset.sum_mul]
    _ =
      h3WeakTestVectorPhysicalL2L1Norm φ
        *
      h3UnitViscosityZeroRHSBound E := by
      rfl

/-- Absolute-value form of the preceding pointwise weak-pairing estimate. -/
theorem abs_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    |h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
        hNS ht hEnd hTail φ q|
      ≤
    h3WeakTestVectorPhysicalL2L1Norm φ
      *
    h3UnitViscosityZeroRHSBound E := by
  simpa only [Real.norm_eq_abs] using
    norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed_le
      hNS ht hEnd hE hTail φ q

/-- On the physical elapsed interval, the ambient-real projected-RHS weak
pairing inherits the same constant pointwise majorant. -/
theorem abs_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_le_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hr : r ∈ Set.Icc (0 : ℝ) tau) :
    |h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
        hNS ht hEnd hTail φ r|
      ≤
    h3WeakTestVectorPhysicalL2L1Norm φ
      *
    h3UnitViscosityZeroRHSBound E := by
  rw [
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_apply_of_mem
      hNS ht hEnd hTail φ hr
  ]

  exact
    abs_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed_le
      hNS ht hEnd hE hTail φ ⟨r, hr⟩

end

end Euclidean
end Bridge
end PrimeTensor
