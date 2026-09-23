import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedVelocityOldBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedPhysicalL2EnergyAxisBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongOldRHSDecomposition
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongAdvectionRepresentatives

/-!
# Old physical L² pairings: canonical zeroth-order energy coefficients

At one old canonical elapsed slice, package the physical velocity, Laplacian,
and Leray forcing in the native three-component `PiLp 2` Hilbert space.

The physical representatives already satisfy:

* velocity coordinate = the old logged velocity component a.e.;
* Laplacian coordinate = the old classical Laplacian a.e.;
* unprojected nonlinear coordinate = the old classical advection a.e.;
* the old velocity is Leray-fixed, so pairing it with Leray forcing equals
  pairing it with unprojected advection.

Expanding the finite Hilbert inner product, applying these representative
identities, and reindexing `Fin 3` by the established equivalence with
`Axis Depth.three` identifies the two Hilbert coefficients with the canonical
zeroth-order diffusion and transport energy derivatives.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3PathOldPhysicalL2PairingBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOldPhysicalL2PairingBridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Twice the old physical velocity/Laplacian Hilbert pairing is exactly the
canonical zeroth-order diffusion energy contribution. -/
theorem two_inner_h3PreterminalCanonicalVelocity_oldLaplacian_eq_velocityH3DiffusionDerivative0At
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    2 * inner ℝ
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      (h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      =
    velocityH3DiffusionDerivative0At
      u (t + (q : ℝ)) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

  let L : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

  have hVae
      (i : Fin 3) :
      ((V i : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u (t + (q : ℝ)) (h3AxisOfFin3 i) := by
    dsimp only [
      V,
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed,
      PiLp.toLp_apply
    ]
    exact
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_old_pressureFree
        hNS ht hEnd hTail q i

  have hLae
      (i : Fin 3) :
      ((L i : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        momentumDiffusion0Component
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          (h3AxisOfFin3 i)
          x) := by
    dsimp only [
      L,
      h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed,
      PiLp.toLp_apply
    ]

    have hOld :=
      h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed_ae_eq_old
        hNS ht hEnd hTail q i

    filter_upwards [hOld] with x hx

    rw [hx]

    unfold momentumDiffusion0Component
    simp only [
      Fin.sum_univ_three,
      h3AxisOfFin3_zero,
      h3AxisOfFin3_one,
      h3AxisOfFin3_two
    ]

    have hComponent :
        loggedVelocityComponent
            u (t + (q : ℝ)) (h3AxisOfFin3 i)
          =
        (fun y : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component
              (h3AxisOfFin3 i)) := by
      unfold loggedVelocityComponent
      rfl

    rw [hComponent]

    symm

    simpa only [add_assoc] using
      (laplacian3_eq
        (fun y : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component
              (h3AxisOfFin3 i))
        x)

  have hCoord
      (i : Fin 3) :
      inner ℝ (V i) (L i)
        =
      ∫ x : Point3,
        loggedVelocityComponent
            u (t + (q : ℝ)) (h3AxisOfFin3 i) x
          *
        momentumDiffusion0Component
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            (h3AxisOfFin3 i)
            x
        ∂volume := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hVae i, hLae i] with x hVx hLx
    rw [hVx, hLx]
    exact mul_comm _ _

  have hInner :
      inner ℝ V L
        =
      ∑ i : Fin 3,
        ∫ x : Point3,
          loggedVelocityComponent
              u (t + (q : ℝ)) (h3AxisOfFin3 i) x
            *
          momentumDiffusion0Component
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              (h3AxisOfFin3 i)
              x
          ∂volume := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact hCoord i

  rw [show
    2 * inner ℝ
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      (h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      =
    2 * inner ℝ V L by rfl]

  rw [hInner]

  calc
    2 *
        (∑ i : Fin 3,
          ∫ x : Point3,
            loggedVelocityComponent
                u (t + (q : ℝ)) (h3AxisOfFin3 i) x
              *
            momentumDiffusion0Component
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                (h3AxisOfFin3 i)
                x
            ∂volume)
        =
      ∑ i : Fin 3,
        spatialEnergyPairing
          (loggedVelocityComponent
            u (t + (q : ℝ)) (h3AxisOfFin3 i))
          (momentumDiffusion0Component
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            (h3AxisOfFin3 i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rfl
    _ =
      ∑ j : PrimeTensor.Axis Depth.three,
        spatialEnergyPairing
          (loggedVelocityComponent u (t + (q : ℝ)) j)
          (momentumDiffusion0Component
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            j) := by
      exact
        sum_fin3_h3AxisOfFin3_eq_sum_axis_three
          (fun j : PrimeTensor.Axis Depth.three =>
            spatialEnergyPairing
              (loggedVelocityComponent u (t + (q : ℝ)) j)
              (momentumDiffusion0Component
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                j))
    _ =
      velocityH3DiffusionDerivative0At
        u (t + (q : ℝ)) := by
      rfl

/-- Twice the old physical velocity/Leray-forcing Hilbert pairing is exactly
the canonical zeroth-order transport energy contribution. -/
theorem two_inner_h3PreterminalCanonicalVelocity_oldLerayForcing_eq_velocityH3TransportDerivative0At
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    2 * inner ℝ
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      (h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      =
    velocityH3TransportDerivative0At
      u (t + (q : ℝ)) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

  let UOld : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let A : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakStrongAdvectionPhysicalL2Hilbert UOld

  have hVLeray :
      H3PhysicalRealFinVectorL2HilbertLerayFixed V := by
    dsimp only [V]
    exact
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_lerayFixed
        hNS ht hEnd hTail q

  have hProjection :
      inner ℝ V
          (h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
            hNS ht hEnd hTail q)
        =
      inner ℝ V A := by
    have hPair :=
      inner_weakStrongLerayForcing_eq_advection_of_lerayFixed
        UOld
        (by
          dsimp only [UOld]
          exact
            h3PreterminalTailCanonicalSpectralStateOnElapsed_realizable
              hNS ht hEnd hTail q)
        (by
          dsimp only [UOld]
          exact
            h3PreterminalTailCanonicalSpectralStateOnElapsed_rawDivergenceFree
              hNS ht hEnd hTail q)
        V
        hVLeray

    rw [
      h3WeakStrongLerayForcingPhysicalL2Hilbert_oldElapsed_eq
        hNS ht hEnd hTail q
    ] at hPair

    simpa only [A] using hPair

  have hVae
      (i : Fin 3) :
      ((V i : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u (t + (q : ℝ)) (h3AxisOfFin3 i) := by
    dsimp only [
      V,
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed,
      PiLp.toLp_apply
    ]
    exact
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_old_pressureFree
        hNS ht hEnd hTail q i

  have hAae
      (i : Fin 3) :
      ((A i : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        momentumTransport0Component
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          (h3AxisOfFin3 i)
          x) := by
    have hOld :=
      h3WeakStrongAdvectionPhysicalL2_oldElapsed_ae
        hNS ht hEnd hTail q i

    dsimp only [
      A,
      h3WeakStrongAdvectionPhysicalL2Hilbert,
      PiLp.toLp_apply,
      UOld
    ]

    filter_upwards [hOld] with x hx

    rw [hx]

    unfold
      momentumTransport0Component
      h3PreterminalOldElapsedWeakStrongVelocity

    rfl

  have hCoord
      (i : Fin 3) :
      inner ℝ (V i) (A i)
        =
      ∫ x : Point3,
        loggedVelocityComponent
            u (t + (q : ℝ)) (h3AxisOfFin3 i) x
          *
        momentumTransport0Component
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            (h3AxisOfFin3 i)
            x
        ∂volume := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hVae i, hAae i] with x hVx hAx
    rw [hVx, hAx]
    exact mul_comm _ _

  have hInner :
      inner ℝ V A
        =
      ∑ i : Fin 3,
        ∫ x : Point3,
          loggedVelocityComponent
              u (t + (q : ℝ)) (h3AxisOfFin3 i) x
            *
          momentumTransport0Component
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              (h3AxisOfFin3 i)
              x
          ∂volume := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact hCoord i

  rw [show
    2 * inner ℝ
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      (h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      =
    2 * inner ℝ V
      (h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q) by rfl]

  rw [hProjection, hInner]

  calc
    2 *
        (∑ i : Fin 3,
          ∫ x : Point3,
            loggedVelocityComponent
                u (t + (q : ℝ)) (h3AxisOfFin3 i) x
              *
            momentumTransport0Component
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                (h3AxisOfFin3 i)
                x
            ∂volume)
        =
      ∑ i : Fin 3,
        spatialEnergyPairing
          (loggedVelocityComponent
            u (t + (q : ℝ)) (h3AxisOfFin3 i))
          (momentumTransport0Component
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            (h3AxisOfFin3 i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rfl
    _ =
      ∑ j : PrimeTensor.Axis Depth.three,
        spatialEnergyPairing
          (loggedVelocityComponent u (t + (q : ℝ)) j)
          (momentumTransport0Component
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            j) := by
      exact
        sum_fin3_h3AxisOfFin3_eq_sum_axis_three
          (fun j : PrimeTensor.Axis Depth.three =>
            spatialEnergyPairing
              (loggedVelocityComponent u (t + (q : ℝ)) j)
              (momentumTransport0Component
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                j))
    _ =
      velocityH3TransportDerivative0At
        u (t + (q : ℝ)) := by
      rfl

end

end Euclidean
end Bridge
end PrimeTensor
