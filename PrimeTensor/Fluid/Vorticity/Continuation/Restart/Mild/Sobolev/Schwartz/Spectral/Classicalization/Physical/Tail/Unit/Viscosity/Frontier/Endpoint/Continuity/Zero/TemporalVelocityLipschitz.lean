import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalVelocityDifferenceBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Lipschitz

/-!
# Zeroth-order endpoint continuity: close the local Lipschitz target

`TemporalVelocityDifferenceBound` proves the genuine arbitrary-pair strong
physical Hilbert estimate

    ‖U(q) - U(r)‖
      ≤
    3 * C(E) * (q-r)

for ordered elapsed times `r ≤ q`, under the family-level pressure-gradient
defect mass frontier.

This file projects that estimate to each physical scalar `L²` velocity
coordinate.  The intermediate Hilbert states were defined as increments from
elapsed zero, so after coordinate projection the common zero anchor cancels:

    [(u_j(q)-u_j(0)) - (u_j(r)-u_j(0))]
      =
    u_j(q)-u_j(r).

`PiLp.norm_apply_le` then transfers the Hilbert bound to each zeroth-order jet.
A case split on the order of two elapsed times converts the ordered estimate to
the symmetric metric statement required by `LipschitzWith`.

Thus the family-level pressure-defect mass frontier implies the exact existing
local zeroth-order Lipschitz predicate.  No Fourier increment hypothesis and no
endpoint continuity assumption are used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroTemporalVelocityLipschitz
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Ordered elapsed times inherit the strong scalar physical `L²` difference
bound from the three-component Hilbert estimate. -/
theorem dist_h3PreterminalCanonicalL2JetOnElapsed_slot0_le_three_mul_rhsBound_mul_dist_of_le_of_allPressureDefect
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
      norm_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_sub_le_of_allPressureDefect
        hNS ht htau hEnd hE hTail hPressure r q hrq

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

/-- The family-level pressure-defect mass frontier closes the existing local
zeroth-order physical `L²` Lipschitz target. -/
theorem h3PreterminalCanonicalL2ZeroLipschitzOnElapsed_of_allDivergenceFreePressureDefect
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
        hNS ht hEnd hTail) :
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
      dist_h3PreterminalCanonicalL2JetOnElapsed_slot0_le_three_mul_rhsBound_mul_dist_of_le_of_allPressureDefect
        hNS ht htau hEnd hE hTail hPressure
        j r q hrq

  · have h :=
      dist_h3PreterminalCanonicalL2JetOnElapsed_slot0_le_three_mul_rhsBound_mul_dist_of_le_of_allPressureDefect
        hNS ht htau hEnd hE hTail hPressure
        j q r hqr

    simpa only [dist_comm] using h

end

end Euclidean
end Bridge
end PrimeTensor
