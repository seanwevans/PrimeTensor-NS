import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalProjectedRHSHilbertBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family

/-!
# Zeroth-order endpoint continuity: Hilbert pairing form of the weak increment bound

`TemporalProjectedRHSHilbertBound` gives a quantitative estimate for the literal
old velocity increment paired with one compact smooth divergence-free test.

The density step should act on the actual physical `PiLp 2` velocity increment

    U(q) - U(0).

This file identifies the Hilbert pairing with that intermediate physical
increment directly with the literal old spatial pairing from the endpoint-
independent FTC branch.  It then transfers the existing estimate to the native
Hilbert pairing.

No endpoint `L²` continuity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroProjectedRHSWeakHilbertPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroProjectedRHSWeakHilbertPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Pairing a compact smooth physical weak-test vector with the genuine
intermediate physical velocity increment is exactly the literal old velocity
increment pairing used by the endpoint-independent FTC branch. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_eq_oldIntegralDifference_zero
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + (q : ℝ)) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume := by
  rw [PiLp.inner_apply]

  apply Finset.sum_congr rfl
  intro i hi

  rw [
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_apply
      hNS ht htau hEnd hTail q i
  ]

  unfold h3WeakTestVectorPhysicalL2Hilbert

  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  have hφ :
      ((h3WeakTestFunctionPhysicalL2 (φ i) : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (φ i : Point3 → ℝ) :=
    h3WeakTestFunctionPhysicalL2_ae (φ i)

  have hqOld :
      ((h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i) q : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i) :=
    h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_loggedVelocityComponent
      hNS ht hEnd hTail q i

  let q0 : Set.Icc (0 : ℝ) tau :=
    ⟨0, ⟨le_rfl, htau.le⟩⟩

  have h0Old :
      ((h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i) q0 : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        t
        (h3AxisOfFin3 i) := by
    have h :=
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_loggedVelocityComponent
        hNS ht hEnd hTail q0 i

    simpa only [q0, add_zero] using h

  have hIncrementOld :
      ((((h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 i) q : H3ScalarL2)
          -
        (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 i) q0 : H3ScalarL2)) : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      fun x : Point3 =>
        loggedVelocityComponent
            u (t + (q : ℝ)) (h3AxisOfFin3 i) x
          -
        loggedVelocityComponent
            u t (h3AxisOfFin3 i) x := by
    exact
      (Lp.coeFn_sub
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i) q)
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i) q0)).trans
        (hqOld.sub h0Old)

  filter_upwards [hφ, hIncrementOld] with x hxφ hxIncrement

  rw [hxφ, hxIncrement]

  simp [mul_comm]

/-- Native Hilbert-space form of the quantitative divergence-free weak
velocity-increment estimate. -/
theorem norm_inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_le_of_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau)
    (hPressure :
      H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ) :
    ‖inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)‖
      ≤
    ((3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    (q : ℝ) := by
  rw [
    inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_eq_oldIntegralDifference_zero
      hNS ht htau hEnd hTail φ q
  ]

  exact
    norm_h3PreterminalLoggedVelocity_weakPairingDifference_le_three_mul_hilbertNorm_of_pressureDefect
      hNS ht hEnd hE hTail
      φ hφ q.property hPressure

end

end Euclidean
end Bridge
end PrimeTensor
