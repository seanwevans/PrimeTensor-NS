import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOldPhysicalL2PairingBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedPhysicalL2EnergyGermBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathPressureCancellationZero
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathPDEPairingL2Closure

/-!
# Selected order-zero coefficient: identification with the canonical formal derivative

The selected physical kinetic-energy derivative has coefficient

    2 * ⟪S(q), R_selected(q)⟫.

At every positive overlap point, both physical factors have already been
identified exactly with their old canonical counterparts.  The old projected
RHS is the physical Laplacian minus the physical Leray forcing, and the
preceding pairing bridge identifies those two pairings with the canonical
zeroth-order diffusion and transport energy terms.

Finally, on an H³ energy-class time, the already-closed pressure cancellation
and PDE pairing frontiers give

    diffusion - transport
      = formal zeroth-order time derivative.

Thus the selected strong derivative coefficient is exactly
`velocityH3FormalDerivative0At` at the corresponding old absolute time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedOrderZeroCoefficientBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The old physical projected-RHS pairing is exactly diffusion minus
transport at the corresponding absolute time. -/
theorem two_inner_h3PreterminalCanonicalVelocity_oldProjectedRHS_eq_diffusion_sub_transport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {S t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u S)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hEnd : t + tau < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (q : Set.Icc (0 : ℝ) tau) :
    2 * inner ℝ
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      =
    velocityH3DiffusionDerivative0At u (t + (q : ℝ))
      -
    velocityH3TransportDerivative0At u (t + (q : ℝ)) := by
  have hProjected :=
    inner_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_eq
      hNS ht hEnd hTail q
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)

  calc
    2 * inner ℝ
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
        =
      2 *
        (inner ℝ
            (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
              hNS ht hEnd hTail q)
            (h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
              hNS ht hEnd hTail q)
          -
         inner ℝ
            (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
              hNS ht hEnd hTail q)
            (h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
              hNS ht hEnd hTail q)) := by
          exact congrArg (fun z : ℝ => 2 * z) hProjected
    _ =
      2 * inner ℝ
          (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
            hNS ht hEnd hTail q)
          (h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
            hNS ht hEnd hTail q)
        -
      2 * inner ℝ
          (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
            hNS ht hEnd hTail q)
          (h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
            hNS ht hEnd hTail q) := by
          ring
    _ =
      velocityH3DiffusionDerivative0At u (t + (q : ℝ))
        -
      velocityH3TransportDerivative0At u (t + (q : ℝ)) := by
          rw [
            two_inner_h3PreterminalCanonicalVelocity_oldLaplacian_eq_velocityH3DiffusionDerivative0At
              hNS ht hEnd hTail q,
            two_inner_h3PreterminalCanonicalVelocity_oldLerayForcing_eq_velocityH3TransportDerivative0At
              hNS ht hEnd hTail q
          ]

/-- On a strict H³ energy-class time, the old physical projected-RHS pairing
is exactly the canonical formal zeroth-order energy derivative. -/
theorem two_inner_h3PreterminalCanonicalVelocity_oldProjectedRHS_eq_velocityH3FormalDerivative0At
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {S t tau T a : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u S)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hEnd : t + tau < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (q : Set.Icc (0 : ℝ) tau)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hsClass : t + (q : ℝ) ∈ Set.Ioo a T) :
    2 * inner ℝ
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      =
    velocityH3FormalDerivative0At u (t + (q : ℝ)) := by
  let s : ℝ := t + (q : ℝ)

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass hsClass

  have hsAbs :
      s ∈ Set.Ioo (0 : ℝ) T := by
    dsimp only [s]
    exact
      ⟨
        lt_trans hClass.terminal_start.1 hsClass.1,
        hsClass.2
      ⟩

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressureAt_navierStokes
        hClass hsClass

  have hPairing :
      H3PDEPairingIntegrableAt u p s := by
    dsimp only [p, s]
    exact
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
        u T hH3 a hClass
        (t + (q : ℝ)) hsClass

  have hPressureZero :
      velocityH3PressureDerivative0At u p s = 0 := by
    dsimp only [p, s]
    exact
      h3PathEnergyClassProducesPressure0Cancellation_closed
        u T hH3 a hClass
        (t + (q : ℝ)) hsClass

  have hFormalPDE :
      velocityH3FormalDerivative0At u s
        =
      velocityH3PDEDerivative0At u p s :=
    velocityH3FormalDerivative0At_eq_pde
      hPDE hsAbs

  have hSplit :
      velocityH3PDEDerivative0At u p s
        =
      velocityH3DiffusionDerivative0At u s
        - velocityH3TransportDerivative0At u s
        - velocityH3PressureDerivative0At u p s :=
    velocityH3PDEDerivative0At_eq_split
      hPairing

  have hOld :
      2 * inner ℝ
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
        =
      velocityH3DiffusionDerivative0At u s
        -
      velocityH3TransportDerivative0At u s := by
    dsimp only [s]
    exact
      two_inner_h3PreterminalCanonicalVelocity_oldProjectedRHS_eq_diffusion_sub_transport
        hNS ht hEnd hTail q

  calc
    2 * inner ℝ
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
        =
      velocityH3DiffusionDerivative0At u s
        -
      velocityH3TransportDerivative0At u s :=
      hOld
    _ =
      velocityH3DiffusionDerivative0At u s
        - velocityH3TransportDerivative0At u s
        - velocityH3PressureDerivative0At u p s := by
          rw [hPressureZero]
          ring
    _ =
      velocityH3PDEDerivative0At u p s :=
      hSplit.symm
    _ =
      velocityH3FormalDerivative0At u s :=
      hFormalPDE.symm
    _ =
      velocityH3FormalDerivative0At u (t + (q : ℝ)) := by
      rfl

/-- The actual selected derivative coefficient equals the old canonical formal
zeroth-order derivative at every strict positive overlap time that lies in the
energy class. -/
theorem two_inner_h3PreterminalSelectedVelocity_selectedProjectedRHS_eq_velocityH3FormalDerivative0At
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {S t tau T a q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u S)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (htau : 0 < tau)
    (hEnd : t + tau < S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u S t hNS ht hE hTail)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hsClass : t + q ∈ Set.Ioo a T) :
    2 * inner ℝ
      (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail q)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR q)
      =
    velocityH3FormalDerivative0At u (t + q) := by
  let qClosed : Set.Icc (0 : ℝ) tau :=
    ⟨q, hq.1.le, hq.2.le⟩

  have hSelectedRHS :
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR q
        =
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR qClosed) := by
    simpa only [qClosed] using
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_apply_of_mem
        hNS ht hE hTail htauR
        ⟨hq.1.le, hq.2.le⟩

  have hVelocity :
      h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail q
        =
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail qClosed := by
    simpa only [qClosed] using
      h3PreterminalSelectedVelocityPhysicalL2HilbertAt_eq_canonicalVelocityPhysicalL2HilbertOnElapsed_of_restartRadiusAgreement
        hNS ht hEnd hE hTail htauR hPhysical qClosed hq.1

  have hRHS :
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR qClosed)
        =
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail qClosed := by
    exact
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq_tailCanonical_of_restartRadiusAgreement
        hNS ht hEnd hE hTail htauR hPhysical qClosed hq.1

  rw [hSelectedRHS, hVelocity, hRHS]

  simpa only [qClosed] using
    two_inner_h3PreterminalCanonicalVelocity_oldProjectedRHS_eq_velocityH3FormalDerivative0At
      hNS ht hEnd hTail qClosed
      hH3 hClass hsClass

end

end Euclidean
end Bridge
end PrimeTensor
