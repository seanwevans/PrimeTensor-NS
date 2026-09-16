import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongProjectedRHSEnergyBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldL2EnergyRHSReduction

/-!
# Bridge the concrete weak--strong projected RHS bound into Grönwall

The PDE energy estimate is now concrete:

    2 ⟪D(q), RΔ(q)⟫ ≤ 6 B ‖D(q)‖².

The existing Grönwall closure is written in terms of realized branch paths

    S, O : ℝ → H3PhysicalRealFinVectorL2Hilbert

and their strong derivatives `S'`, `O'`.

This file isolates the one remaining temporal identification:

    S'(q) - O'(q) = RΔ(q).

Together with the already-explicit weak--strong spatial inputs
(selected-gradient bound, interaction integrability, and old-transport IBP),
that identity upgrades the realized branch data directly to

    H3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed

with Grönwall coefficient `K = 6 B`.

No new spatial estimate is proved here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongTransportIntegralBound

noncomputable local instance axisFintypeH3SelectedOldWeakStrongProjectedRHSGronwallBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact remaining data needed to feed the concrete weak--strong
projected-RHS estimate into the branch-local Grönwall package.

The only temporal/PDE identification left is
`derivativeDifference_eq_projectedRHS`.  The other fields are precisely the
spatial hypotheses already consumed by the transport estimate. -/
structure H3PreterminalSelectedOldWeakStrongProjectedRHSDerivativeDataOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hBranches :
      H3PreterminalSelectedOldL2BranchDerivativeDataOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail) where
  B : ℝ
  B_nonneg : 0 ≤ B
  derivativeDifference_eq_projectedRHS :
    ∀ q : Set.Icc (0 : ℝ) tau,
      hBranches.selectedDerivative (q : ℝ)
          - hBranches.oldDerivative (q : ℝ)
        =
      h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q
  selectedGradient_bound :
    ∀
      (q : Set.Icc (0 : ℝ) tau)
      (x : Point3)
      (j i : PrimeTensor.Axis Depth.three),
      abs
        (spatial3.d
          i
          (fun y =>
            ((h3PreterminalSelectedWeakStrongVelocity
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail)
              (q : ℝ) y).component j)
          x)
        ≤
      B
  interaction_integrable :
    ∀ q : Set.Icc (0 : ℝ) tau,
      MeasureTheory.Integrable
        (h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ))
        (volume : Measure Point3)
  oldTransport_integrationByParts :
    ∀ q : Set.Icc (0 : ℝ) tau,
      H3PreterminalSelectedOldWeakStrongTransportIntegrationByPartsAt
        hNS ht hEnd hE hTail q

/-- The concrete weak--strong projected-RHS estimate supplies the exact scalar
energy derivative package consumed by the existing Grönwall theorem. -/
theorem h3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed_of_weakStrongProjectedRHS
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hBranches :
      H3PreterminalSelectedOldL2BranchDerivativeDataOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail)
    (hData :
      H3PreterminalSelectedOldWeakStrongProjectedRHSDerivativeDataOnElapsed
        hNS ht hEnd hE hTail htauR hBranches) :
    H3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail := by
  refine
    ⟨hBranches.selectedPath,
      hBranches.oldPath,
      hBranches.selectedDerivative,
      hBranches.oldDerivative,
      6 * hData.B,
      hBranches.selectedPath_eq,
      hBranches.oldPath_eq,
      hBranches.selectedPath_continuous,
      hBranches.oldPath_continuous,
      hBranches.selectedPath_hasDeriv,
      hBranches.oldPath_hasDeriv,
      ?_⟩

  intro s hs

  let q : Set.Icc (0 : ℝ) tau :=
    ⟨s, hs.1, hs.2.le⟩

  have hPathDifference :
      hBranches.selectedPath s
          - hBranches.oldPath s
        =
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q := by
    dsimp only [q]

    rw [
      hBranches.selectedPath_eq
        ⟨s, hs.1, hs.2.le⟩,
      hBranches.oldPath_eq
        ⟨s, hs.1, hs.2.le⟩
    ]

    rfl

  have hDerivativeDifference :
      hBranches.selectedDerivative s
          - hBranches.oldDerivative s
        =
      h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q := by
    simpa only [q] using
      hData.derivativeDifference_eq_projectedRHS q

  have hProjected :
      2 *
        inner ℝ
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q)
          (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
            hNS ht hEnd hE hTail htauR q)
        ≤
      6 * hData.B *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q‖ ^ 2 := by
    exact
      two_inner_selectedOldUnitProjectedRHSDifference_le_six_mul_norm_sq
        hNS ht hEnd hE hTail htauR q
        hData.B
        hData.B_nonneg
        (hData.selectedGradient_bound q)
        (hData.interaction_integrable q)
        (hData.oldTransport_integrationByParts q)

  rw [hPathDifference, hDerivativeDifference]

  exact hProjected

/-- Once the branch derivatives have been identified with the concrete
unit-viscosity projected RHS difference, the weak--strong estimate closes
physical selected/old agreement by the existing scalar-energy Grönwall
argument. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_weakStrongProjectedRHS
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hBranches :
      H3PreterminalSelectedOldL2BranchDerivativeDataOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail)
    (hData :
      H3PreterminalSelectedOldWeakStrongProjectedRHSDerivativeDataOnElapsed
        hNS ht hEnd hE hTail htauR hBranches)
    (q : Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      (one_pos : (0 : ℝ) < 1)
      (q : ℝ) hNS ht hE hTail := by
  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2EnergyDerivatives
      (one_pos : (0 : ℝ) < 1)
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      htauR
      (h3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed_of_weakStrongProjectedRHS
        hNS
        ht
        hEnd
        hE
        hTail
        htauR
        hBranches
        hData)
      q

end

end Euclidean
end Bridge
end PrimeTensor
