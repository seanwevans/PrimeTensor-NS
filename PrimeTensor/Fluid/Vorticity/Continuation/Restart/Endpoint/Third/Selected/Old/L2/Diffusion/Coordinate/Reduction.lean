import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.L2.Energy.RHS.Reduction

/-!
# Reduce vector diffusion dissipation to three scalar L² pairings

`SelectedOldL2EnergyRHSReduction` isolates the linear part of the selected/old
difference equation and asks only for

    ⟪D, L⟫_ℝ ≤ 0.

The physical velocity space is the finite `PiLp 2` product of three scalar
real `L²` coordinates.  Its inner product is therefore exactly the sum of the
three coordinatewise scalar pairings.

Hence vector diffusion dissipation follows immediately once each coordinate
pairing is nonpositive.  This file performs only that finite-dimensional
reduction.  The remaining analytic diffusion task is now scalar and can be
connected directly to the existing whole-space
`DiffusionPairingIntegrationByParts` machinery.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldL2DiffusionCoordinateReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A three-component physical `L²` pairing is nonpositive whenever every
scalar coordinate pairing is nonpositive. -/
theorem h3PhysicalRealFinVectorL2_inner_nonpos_of_coordinate_nonpos
    (D L : H3PhysicalRealFinVectorL2Hilbert)
    (hCoordinate :
      ∀ i : Fin 3,
        inner ℝ (D i) (L i) ≤ 0) :
    inner ℝ D L ≤ 0 := by
  rw [PiLp.inner_apply]

  exact
    Finset.sum_nonpos
      (fun i _ => hCoordinate i)

/-- RHS data in which diffusion nonpositivity is supplied only coordinatewise.

This is strictly more concrete than the vector-level diffusion sign in
`H3PreterminalSelectedOldL2DifferenceEnergyRHSDataOnElapsed`: the remaining
linear analytic statement is now three scalar `L²` pairings at each time.
-/
def H3PreterminalSelectedOldL2DifferenceCoordinateDiffusionRHSDataOnElapsed
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hBranches :
      H3PreterminalSelectedOldL2BranchDerivativeDataOnElapsed
        hν hNS ht hEnd hE hTail) : Prop :=
  ∃
    (linearDifference :
      ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (transportDifference :
      ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (K : ℝ),
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        hBranches.selectedDerivative s
            - hBranches.oldDerivative s
          =
        linearDifference s
          - transportDifference s)
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        ∀ i : Fin 3,
          inner ℝ
            ((hBranches.selectedPath s
              - hBranches.oldPath s) i)
            ((linearDifference s) i)
            ≤
          0)
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        -2 * inner ℝ
          (hBranches.selectedPath s
            - hBranches.oldPath s)
          (transportDifference s)
          ≤
        K *
          ‖hBranches.selectedPath s
            - hBranches.oldPath s‖ ^ 2)

/-- Coordinatewise diffusion dissipation supplies the vector-level RHS
reduction consumed by the scalar energy Grönwall closure. -/
theorem h3PreterminalSelectedOldL2DifferenceEnergyRHSDataOnElapsed_of_coordinateDiffusion
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hBranches :
      H3PreterminalSelectedOldL2BranchDerivativeDataOnElapsed
        hν hNS ht hEnd hE hTail)
    (hCoordinate :
      H3PreterminalSelectedOldL2DifferenceCoordinateDiffusionRHSDataOnElapsed
        hν hNS ht hEnd hE hTail hBranches) :
    H3PreterminalSelectedOldL2DifferenceEnergyRHSDataOnElapsed
      hν hNS ht hEnd hE hTail hBranches := by
  rcases hCoordinate with
    ⟨linearDifference, transportDifference, K,
      hDerivativeDifference,
      hDiffusionCoordinate,
      hTransport⟩

  refine
    ⟨linearDifference,
      transportDifference,
      K,
      hDerivativeDifference,
      ?_,
      hTransport⟩

  intro s hs

  exact
    h3PhysicalRealFinVectorL2_inner_nonpos_of_coordinate_nonpos
      (hBranches.selectedPath s
        - hBranches.oldPath s)
      (linearDifference s)
      (hDiffusionCoordinate s hs)

/-- The coordinatewise diffusion frontier together with the transport-energy
bound already closes selected/old physical agreement at every positive time of
the strict elapsed interval. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_l2CoordinateDiffusionRHS
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius ν E)
    (hBranches :
      H3PreterminalSelectedOldL2BranchDerivativeDataOnElapsed
        hν hNS ht hEnd hE hTail)
    (hCoordinate :
      H3PreterminalSelectedOldL2DifferenceCoordinateDiffusionRHSDataOnElapsed
        hν hNS ht hEnd hE hTail hBranches)
    (q : Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      hν (q : ℝ) hNS ht hE hTail := by
  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2EnergyRHSReduction
      hν
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      htauR
      hBranches
      (h3PreterminalSelectedOldL2DifferenceEnergyRHSDataOnElapsed_of_coordinateDiffusion
        hν
        hNS
        ht
        hEnd
        hE
        hTail
        hBranches
        hCoordinate)
      q

end

end Euclidean
end Bridge
end PrimeTensor
