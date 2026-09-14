import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.ForcingWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Projected.RHS.Pairing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Old.Momentum

/-!
# Zeroth-order endpoint continuity: old weak diffusion

The nonlinear half of the old weak projected RHS is now endpoint-independent:
against divergence-free compact tests, the Leray-projected nonlinear forcing
equals old physical advection.

This file closes the matching diffusion half.

The existing weak diffusion functional

    h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed

is already endpoint-independent: it is written only in terms of twice
differentiated compact tests paired with the old slot-0 physical `L²` velocity.

At one old elapsed slice we:

* identify the slot-0 Hilbert pairing directly with the old logged velocity;
* use the generic twofold spatial integration-by-parts theorem to move the
  derivatives back from the compact test onto the old velocity;
* sum the three coordinate directions and use the existing dimension-three
  `RealFluid.laplacianVector` bridge.

Therefore the endpoint-independent weak diffusion functional is exactly the
literal old physical `Δu` pairing on every closed elapsed slice.

No endpoint continuity, selected restart, mild equation, or temporal
regularity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldWeakDiffusion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldWeakDiffusion :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A compact smooth scalar test paired with the old slot-0 physical `L²`
state is exactly its literal spatial pairing with the old logged velocity. -/
theorem h3WeakTestFunctionPhysicalL2_inner_preterminalSlot0_eq_integral_old
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 ψ)
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 i) q)
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)
          x)
      ∂volume := by
  let Φ : H3ScalarL2 :=
    h3WeakTestFunctionPhysicalL2 ψ

  let V : H3ScalarL2 :=
    h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot0 i) q

  have hΦ :
      (Φ : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (ψ : Point3 → ℝ) := by
    dsimp only [Φ]
    exact h3WeakTestFunctionPhysicalL2_ae ψ

  have hV :
      (V : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i) := by
    dsimp only [V]
    exact
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_loggedVelocityComponent
        hNS ht hEnd hTail q i

  change
    inner ℝ Φ V
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)
          x)
      ∂volume

  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [hΦ, hV] with x hxΦ hxV

  rw [hxΦ, hxV]

  simpa [mul_comm]

/-- The existing endpoint-independent weak diffusion functional is exactly the
literal old physical Laplacian pairing. -/
theorem h3PreterminalTailCanonicalZeroWeakDiffusionPairingOnElapsed_eq_oldLaplacian
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestVector) :
    h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
        hNS ht hEnd hTail φ q
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))
        ∂volume := by
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  unfold h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed

  apply Finset.sum_congr rfl

  intro i hi

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hOldC3 :
      SpatialC3
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)) := by
    unfold loggedVelocityComponent

    exact
      hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ))
        hAbs
        (h3AxisOfFin3 i)

  have hOldC2 :
      SpatialC2
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)) :=
    hOldC3.of_le (by norm_num)

  have hTerm
      (k : Fin 3) :
      inner ℝ
          (h3WeakTestFunctionPhysicalL2
            (h3WeakTestFunctionSecondSpatialDerivative
              (h3AxisOfFin3 k)
              (φ i)))
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 i) q)
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (loggedVelocityComponent
                u
                (t + (q : ℝ))
                (h3AxisOfFin3 i)))
            x)
        ∂volume := by
    have hInner :=
      h3WeakTestFunctionPhysicalL2_inner_preterminalSlot0_eq_integral_old
        hNS ht hEnd hTail
        (h3WeakTestFunctionSecondSpatialDerivative
          (h3AxisOfFin3 k)
          (φ i))
        q i

    have hTransfer :=
      h3SpatialC2_test_pairing_secondSpatialDerivative_eq_testSecondDerivative_pairing
        hOldC2
        (h3AxisOfFin3 k)
        (φ i)

    exact hInner.trans hTransfer.symm

  have hD
      (k : Fin 3) :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 i)))
              x))
        (volume : Measure Point3) := by
    exact
      h3SpatialC2_test_mul_secondSpatialDerivative_integrable
        hOldC2
        (h3AxisOfFin3 k)
        (φ i)

  calc
    (∑ k : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSecondSpatialDerivative
            (h3AxisOfFin3 k)
            (φ i)))
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 i) q))
        =
      ∑ k : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 i)))
              x)
          ∂volume := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hTerm k
    _ =
      ∫ x : Point3,
        ∑ k : Fin 3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 i)))
              x)
        ∂volume := by
      symm
      exact
        integral_finset_sum
          (Finset.univ : Finset (Fin 3))
          (fun k _ => hD k)
    _ =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (∑ k : Fin 3,
            spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 i)))
              x)
        ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      change
        (∑ k : Fin 3,
          (φ i x) *
            spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 i)))
              x)
          =
        (φ i x) *
          ∑ k : Fin 3,
            spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 i)))
              x
      rw [Finset.mul_sum]
    _ =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))
        ∂volume := by
      apply integral_congr_ae
      filter_upwards with x

      have hLap :=
        realFluid_laplacianVector_component_eq_fin_sum_three_endpoint
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          x
          (h3AxisOfFin3 i)

      change
        (φ i x) *
          (∑ k : Fin 3,
            spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 i)))
              x)
          =
        (φ i x) *
          (PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i)

      rw [hLap]

      rfl

end

end Euclidean
end Bridge
end PrimeTensor
