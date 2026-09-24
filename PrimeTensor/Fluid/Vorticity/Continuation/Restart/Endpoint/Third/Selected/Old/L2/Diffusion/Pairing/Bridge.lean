import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.L2.Diffusion.Coordinate.Reduction
import PrimeTensor.Fluid.Vorticity.H3.Energy.Diffusion

/-!
# Bridge scalar physical L² diffusion pairings to the existing IBP API

`SelectedOldL2DiffusionCoordinateReduction` reduced vector diffusion
dissipation to three scalar real `L²` inequalities.

The older H³ energy development already contains the exact whole-space
integration-by-parts statement we need:

    DiffusionPairingIntegrationByParts f g

for concrete scalar fields `f,g`.

This file supplies the quotient bridge.  If scalar `L²` classes `F,G` admit
a.e. representatives `f,g` satisfying that existing IBP identity, then

    ⟪F,G⟫_ℝ ≤ 0.

The proof simply identifies the Mathlib `L²` inner product with
`∫ f*g`, while `spatialEnergyPairing f g` is `2 * ∫ f*g`.

Thus no new diffusion analysis is introduced here.  The remaining task is to
identify the selected-minus-old velocity coordinate and its Laplacian
difference with the concrete fields to which the existing whole-space IBP
machinery applies.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldL2DiffusionPairingBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldL2DiffusionPairingBridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Quotient-safe realization of one scalar `L²` diffusion pairing by concrete
whole-space fields carrying the existing exact integration-by-parts identity. -/
def H3ScalarL2DiffusionPairingData
    (F G : H3ScalarL2) : Prop :=
  ∃ f g : ScalarField3,
    ((F : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
      f)
      ∧
    ((G : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
      g)
      ∧
    DiffusionPairingIntegrationByParts f g

/-- The real `L²` inner product agrees with the literal product integral of any
chosen a.e. representatives. -/
theorem h3ScalarL2_inner_eq_integral_mul_of_ae
    (F G : H3ScalarL2)
    {f g : ScalarField3}
    (hF :
      (F : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      f)
    (hG :
      (G : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      g) :
    inner ℝ F G
      =
    ∫ x : Point3, f x * g x ∂volume := by
  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [hF, hG] with x hxF hxG

  rw [hxF, hxG]

  simp [RCLike.inner_apply, mul_comm]

/-- Existing concrete-field diffusion IBP data implies nonpositivity of the
corresponding scalar physical `L²` pairing. -/
theorem h3ScalarL2_inner_nonpos_of_diffusionPairingData
    (F G : H3ScalarL2)
    (hData :
      H3ScalarL2DiffusionPairingData F G) :
    inner ℝ F G ≤ 0 := by
  rcases hData with
    ⟨f, g, hF, hG, hIBP⟩

  have hConcrete :
      spatialEnergyPairing f g ≤ 0 :=
    diffusionPairing_nonpos hIBP

  have hInner :
      inner ℝ F G
        =
      ∫ x : Point3, f x * g x ∂volume :=
    h3ScalarL2_inner_eq_integral_mul_of_ae
      F G hF hG

  unfold spatialEnergyPairing at hConcrete

  rw [hInner]

  linarith

/-- RHS reduction in which scalar diffusion nonpositivity is supplied by the
existing concrete-field whole-space IBP package.

At every time and coordinate, the selected-minus-old physical `L²` difference
and the corresponding linear-diffusion coordinate need only be connected a.e.
to concrete scalar fields satisfying `DiffusionPairingIntegrationByParts`. -/
def H3PreterminalSelectedOldL2DifferenceDiffusionPairingRHSDataOnElapsed
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
          H3ScalarL2DiffusionPairingData
            ((hBranches.selectedPath s
              - hBranches.oldPath s) i)
            ((linearDifference s) i))
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

/-- Concrete scalar-field IBP data supplies the coordinatewise diffusion
nonpositivity required by the previous reduction. -/
theorem h3PreterminalSelectedOldL2DifferenceCoordinateDiffusionRHSDataOnElapsed_of_diffusionPairing
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
    (hPairing :
      H3PreterminalSelectedOldL2DifferenceDiffusionPairingRHSDataOnElapsed
        hν hNS ht hEnd hE hTail hBranches) :
    H3PreterminalSelectedOldL2DifferenceCoordinateDiffusionRHSDataOnElapsed
      hν hNS ht hEnd hE hTail hBranches := by
  rcases hPairing with
    ⟨linearDifference, transportDifference, K,
      hDerivativeDifference,
      hDiffusionPairing,
      hTransport⟩

  refine
    ⟨linearDifference,
      transportDifference,
      K,
      hDerivativeDifference,
      ?_,
      hTransport⟩

  intro s hs i

  exact
    h3ScalarL2_inner_nonpos_of_diffusionPairingData
      ((hBranches.selectedPath s
        - hBranches.oldPath s) i)
      ((linearDifference s) i)
      (hDiffusionPairing s hs i)

/-- The existing scalar whole-space diffusion IBP package, together with the
transport-energy estimate, is enough to close selected/old physical agreement
once the branch derivatives and concrete representatives have been identified. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_l2DiffusionPairingRHS
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
    (hPairing :
      H3PreterminalSelectedOldL2DifferenceDiffusionPairingRHSDataOnElapsed
        hν hNS ht hEnd hE hTail hBranches)
    (q : Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      hν (q : ℝ) hNS ht hE hTail := by
  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2CoordinateDiffusionRHS
      hν
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      htauR
      hBranches
      (h3PreterminalSelectedOldL2DifferenceCoordinateDiffusionRHSDataOnElapsed_of_diffusionPairing
        hν
        hNS
        ht
        hEnd
        hE
        hTail
        hBranches
        hPairing)
      q

end

end Euclidean
end Bridge
end PrimeTensor
