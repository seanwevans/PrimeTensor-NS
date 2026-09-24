import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Velocity.Curl.Lipschitz.Pair
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Lipschitz

/-!
# Close the zeroth-order endpoint Lipschitz frontier by the pressure-free curl route

`SelectedOldWeakStrongOldVelocityCurlLipschitzPair` proves the genuine
arbitrary-pair physical Hilbert estimate

    ‖U(q) - U(r)‖
      ≤
    3 * C(E) * (q-r)

for ordered elapsed times `r ≤ q`, directly from the canonical H³ tail and the
pressure-free curl/vorticity argument.

The existing zeroth-order endpoint interface asks for one common
`LipschitzWith K` bound on the three physical scalar `L²` velocity coordinates.

This file projects the new Hilbert estimate to each coordinate with
`PiLp.norm_apply_le`, converts ordered differences to the symmetric metric
form, and closes that exact existing interface with

    K = 3 * C(E).

Consequently the complete global zeroth-order Lipschitz frontier, and hence the
global zeroth-order strong continuity frontier, are proved without:

* endpoint continuity;
* a pressure-gradient mass hypothesis;
* old Hilbert-valued RHS Bochner integrability.

After this increment, the reduced endpoint-continuity program has only the
ordered-third continuity frontier left.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldVelocityCurlLipschitzClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- For ordered elapsed times, each zeroth physical scalar `L²` coordinate
inherits the new pressure-free Hilbert velocity bound. -/
theorem dist_h3PreterminalCanonicalL2JetOnElapsed_slot0_le_three_mul_rhsBound_mul_dist_of_le_tailH3_curl
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (j : Fin 3)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    dist
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q)
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) r)
      ≤
    (3 * h3UnitViscosityZeroRHSBound E)
      *
    dist q r := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      -
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail r

  have hVector :
      ‖V‖
        ≤
      (3 * h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
    dsimp only [V]
    exact
      norm_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_sub_le_tailH3_curl
        hNS ht htau hEnd hE hTail r q hrq

  have hCoord :
      ‖V j‖ ≤ ‖V‖ :=
    PiLp.norm_apply_le V j

  have hCoordEq :
      V j
        =
      h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q
        -
      h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) r := by
    dsimp only [V]
    rw [
      PiLp.sub_apply,
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_apply
        hNS ht htau hEnd hTail q j,
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_apply
        hNS ht htau hEnd hTail r j
    ]
    abel

  have hScalar :
      ‖h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) r‖
        ≤
      (3 * h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
    rw [hCoordEq] at hCoord
    exact hCoord.trans hVector

  have hDistTime :
      dist q r
        =
      (q : ℝ) - (r : ℝ) := by
    change
      dist (q : ℝ) (r : ℝ)
        =
      (q : ℝ) - (r : ℝ)
    rw [
      Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hrq)
    ]

  rw [dist_eq_norm, hDistTime]
  exact hScalar

/-- The canonical H³ tail alone closes the existing local zeroth-order physical
`L²` Lipschitz predicate. -/
theorem h3PreterminalCanonicalL2ZeroLipschitzOnElapsed_tailH3_curl
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalCanonicalL2ZeroLipschitzOnElapsed
      hNS ht hEnd hTail := by
  let K : ℝ≥0 :=
    ⟨
      3 * h3UnitViscosityZeroRHSBound E,
      mul_nonneg
        (by norm_num)
        (h3UnitViscosityZeroRHSBound_nonneg hE)
    ⟩

  refine ⟨K, ?_⟩
  intro j

  apply LipschitzWith.of_dist_le_mul
  intro q r

  change
    dist
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q)
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) r)
      ≤
    (3 * h3UnitViscosityZeroRHSBound E)
      *
    dist q r

  rcases le_total (r : ℝ) (q : ℝ) with hrq | hqr

  · exact
      dist_h3PreterminalCanonicalL2JetOnElapsed_slot0_le_three_mul_rhsBound_mul_dist_of_le_tailH3_curl
        hNS ht htau hEnd hE hTail
        j r q hrq

  · have h :=
      dist_h3PreterminalCanonicalL2JetOnElapsed_slot0_le_three_mul_rhsBound_mul_dist_of_le_tailH3_curl
        hNS ht htau hEnd hE hTail
        j q r hqr

    simpa only [dist_comm] using h

/-- Therefore the canonical H³ tail alone also closes the local zeroth-order
strong-continuity predicate. -/
theorem h3PreterminalCanonicalL2ZeroContinuousOnElapsed_tailH3_curl
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalCanonicalL2ZeroContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2ZeroContinuousOnElapsed_of_lipschitz
      hNS ht hEnd hTail
      (h3PreterminalCanonicalL2ZeroLipschitzOnElapsed_tailH3_curl
        hNS ht htau hEnd hE hTail)

/-- The pressure-free curl argument closes the radius-wide zeroth-order
Lipschitz frontier outright. -/
theorem H3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius_tailH3_curl
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  exact
    h3PreterminalCanonicalL2ZeroLipschitzOnElapsed_tailH3_curl
      hNS ht hqPos hEnd hE hTail

/-- Hence the global zeroth-order unit-viscosity Lipschitz frontier is proved. -/
theorem H3PreterminalTailUnitViscosityZeroLipschitzFrontier_tailH3_curl :
    H3PreterminalTailUnitViscosityZeroLipschitzFrontier := by
  intro E hE u T t hNS ht hTail

  exact
    H3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius_tailH3_curl
      hNS ht hE hTail

/-- Consequently the global zeroth-order strong-continuity frontier is proved
with no pressure or endpoint-continuity assumption. -/
theorem H3PreterminalTailUnitViscosityZeroContinuityFrontier_tailH3_curl :
    H3PreterminalTailUnitViscosityZeroContinuityFrontier := by
  exact
    h3PreterminalTailUnitViscosityZeroContinuityFrontier_of_lipschitz
      H3PreterminalTailUnitViscosityZeroLipschitzFrontier_tailH3_curl

/-- The closed continuation boundary is now reduced entirely to the existing
ordered-third continuity frontier. -/
theorem h3ControlProducesExtension_of_unitViscosityThirdContinuityClosed_tailH3_curl
    (hThird :
      H3PreterminalTailUnitViscosityThirdContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroLipschitzThirdContinuityClosed
      H3PreterminalTailUnitViscosityZeroLipschitzFrontier_tailH3_curl
      hThird

end

end Euclidean
end Bridge
end PrimeTensor
