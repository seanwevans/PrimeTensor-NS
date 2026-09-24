import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.L2.Energy.Gronwall

/-!
# Reduce selected/old L² uniqueness to diffusion sign plus transport energy bound

`SelectedOldL2EnergyGronwall` replaced the overly strong vector estimate

    ‖D'‖ ≤ K ‖D‖

by the natural scalar energy inequality

    2 ⟪D, D'⟫_ℝ ≤ K ‖D‖².

This file exposes the PDE structure inside that scalar inequality.

For the selected/old difference, write

    D  = S - O
    D' = L - N,

where `L` is the linear diffusion difference and `N` is the nonlinear
transport difference after pressure has been removed.

The standard Navier--Stokes uniqueness calculation then needs exactly

    ⟪D, L⟫_ℝ ≤ 0

and

    -2 ⟪D, N⟫_ℝ ≤ K ‖D‖².

No `L² → L²` estimate on the Laplacian is requested.  This is the precise
frontier at which spatial integration by parts and the transport estimate
belong.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldL2EnergyRHSReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pure Hilbert-space algebra behind the selected/old energy estimate. -/
theorem h3PhysicalRealFinVectorL2_two_inner_sub_rhs
    (D L N : H3PhysicalRealFinVectorL2Hilbert) :
    2 * inner ℝ D (L - N)
      =
    2 * inner ℝ D L - 2 * inner ℝ D N := by
  rw [inner_sub_right]
  ring

/-- A dissipative linear term plus the usual transport-energy estimate gives
the scalar Grönwall inequality. -/
theorem h3PhysicalRealFinVectorL2_energy_le_of_diffusion_nonpos_of_transport_bound
    (D L N : H3PhysicalRealFinVectorL2Hilbert)
    (K : ℝ)
    (hDiffusion :
      inner ℝ D L ≤ 0)
    (hTransport :
      -2 * inner ℝ D N
        ≤
      K * ‖D‖ ^ 2) :
    2 * inner ℝ D (L - N)
      ≤
    K * ‖D‖ ^ 2 := by
  rw [h3PhysicalRealFinVectorL2_two_inner_sub_rhs]
  linarith

/-- Branch-local strong derivative data, with no cross-branch estimate bundled
into it.

This separates the analytic tasks cleanly: first realize the selected and old
physical `L²` paths and their strong time derivatives; only afterwards perform
the Navier--Stokes difference-energy calculation. -/
structure H3PreterminalSelectedOldL2BranchDerivativeDataOnElapsed
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) where
  selectedPath :
    ℝ → H3PhysicalRealFinVectorL2Hilbert
  oldPath :
    ℝ → H3PhysicalRealFinVectorL2Hilbert
  selectedDerivative :
    ℝ → H3PhysicalRealFinVectorL2Hilbert
  oldDerivative :
    ℝ → H3PhysicalRealFinVectorL2Hilbert
  selectedPath_eq :
    ∀ q : Set.Icc (0 : ℝ) tau,
      selectedPath (q : ℝ)
        =
      h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        hν hNS ht hE hTail (q : ℝ)
  oldPath_eq :
    ∀ q : Set.Icc (0 : ℝ) tau,
      oldPath (q : ℝ)
        =
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q
  selectedPath_continuous :
    ContinuousOn selectedPath (Set.Icc (0 : ℝ) tau)
  oldPath_continuous :
    ContinuousOn oldPath (Set.Icc (0 : ℝ) tau)
  selectedPath_hasDeriv :
    ∀ s ∈ Set.Ico (0 : ℝ) tau,
      HasDerivWithinAt
        selectedPath
        (selectedDerivative s)
        (Set.Ici s)
        s
  oldPath_hasDeriv :
    ∀ s ∈ Set.Ico (0 : ℝ) tau,
      HasDerivWithinAt
        oldPath
        (oldDerivative s)
        (Set.Ici s)
        s

/-- The exact remaining PDE energy data for one already-realized pair of
selected/old branches.

`linearDifference` is intended to be the componentwise Laplacian difference.
`transportDifference` is intended to be the pressure-free nonlinear difference.
The proposition deliberately asks only for the sign of the former and the
energy pairing bound for the latter. -/
def H3PreterminalSelectedOldL2DifferenceEnergyRHSDataOnElapsed
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
        inner ℝ
          (hBranches.selectedPath s
            - hBranches.oldPath s)
          (linearDifference s)
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

/-- Diffusion sign plus transport energy bound produces exactly the scalar
energy derivative package consumed by `SelectedOldL2EnergyGronwall`. -/
theorem h3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed_of_rhsReduction
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
    (hRHS :
      H3PreterminalSelectedOldL2DifferenceEnergyRHSDataOnElapsed
        hν hNS ht hEnd hE hTail hBranches) :
    H3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed
      hν hNS ht hEnd hE hTail := by
  rcases hRHS with
    ⟨linearDifference, transportDifference, K,
      hDerivativeDifference,
      hDiffusion,
      hTransport⟩

  refine
    ⟨hBranches.selectedPath,
      hBranches.oldPath,
      hBranches.selectedDerivative,
      hBranches.oldDerivative,
      K,
      hBranches.selectedPath_eq,
      hBranches.oldPath_eq,
      hBranches.selectedPath_continuous,
      hBranches.oldPath_continuous,
      hBranches.selectedPath_hasDeriv,
      hBranches.oldPath_hasDeriv,
      ?_⟩

  intro s hs

  have hEnergy :
      2 * inner ℝ
          (hBranches.selectedPath s
            - hBranches.oldPath s)
          (linearDifference s
            - transportDifference s)
        ≤
      K *
        ‖hBranches.selectedPath s
          - hBranches.oldPath s‖ ^ 2 :=
    h3PhysicalRealFinVectorL2_energy_le_of_diffusion_nonpos_of_transport_bound
      (hBranches.selectedPath s
        - hBranches.oldPath s)
      (linearDifference s)
      (transportDifference s)
      K
      (hDiffusion s hs)
      (hTransport s hs)

  rw [← hDerivativeDifference s hs] at hEnergy

  exact hEnergy

/-- The reduced PDE frontier already closes selected/old physical agreement on
every positive time in the strict elapsed interval. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_l2EnergyRHSReduction
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
    (hRHS :
      H3PreterminalSelectedOldL2DifferenceEnergyRHSDataOnElapsed
        hν hNS ht hEnd hE hTail hBranches)
    (q : Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      hν (q : ℝ) hNS ht hE hTail := by
  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2EnergyDerivatives
      hν
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      htauR
      (h3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed_of_rhsReduction
        hν
        hNS
        ht
        hEnd
        hE
        hTail
        hBranches
        hRHS)
      q

end

end Euclidean
end Bridge
end PrimeTensor
