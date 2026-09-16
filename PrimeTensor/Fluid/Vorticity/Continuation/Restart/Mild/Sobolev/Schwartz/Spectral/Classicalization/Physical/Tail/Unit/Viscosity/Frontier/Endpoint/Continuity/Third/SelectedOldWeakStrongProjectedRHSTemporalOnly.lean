import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongProjectedRHSEnergyAutomatic
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldL2EnergyRHSReduction

/-!
# Projected-RHS Grönwall bridge with only the temporal identity exposed

The spatial weak--strong argument is now fully automatic:

    2 ⟪D(q), RΔ(q)⟫
      ≤
    6 B ‖D(q)‖²,

where `B = C₁ (2E)`.

Consequently, for an already-realized pair of strong physical `L²` branch
paths, the old Grönwall bridge no longer needs any selected-gradient,
interaction-integrability, or transport-IBP data.  Its only PDE identification
is

    S'(q) - O'(q) = RΔ(q).

This file records that reduced compatibility theorem.

Important: this is *not* the intended final endpoint frontier.  The strong old
`L²` derivative remains too strong for the endpoint argument.  The purpose of
this checkpoint is to isolate the exact temporal statement that the
endpoint-independent weak FTC machinery must replace.
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

noncomputable local instance axisFintypeH3SelectedOldWeakStrongProjectedRHSTemporalOnly
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- With the automatic projected-RHS quadratic estimate available, an
already-realized pair of strong branch paths needs only the concrete temporal
RHS identity to produce the scalar energy derivative data consumed by
Grönwall. -/
theorem h3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed_of_projectedRHS_auto
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
    (hDerivative :
      ∀ q : Set.Icc (0 : ℝ) tau,
        hBranches.selectedDerivative (q : ℝ)
            - hBranches.oldDerivative (q : ℝ)
          =
        h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q) :
    H3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail := by
  refine
    ⟨hBranches.selectedPath,
      hBranches.oldPath,
      hBranches.selectedDerivative,
      hBranches.oldDerivative,
      6 * h3PreterminalSelectedWeakStrongGradientEnvelope E,
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
    simpa only [q] using hDerivative q

  have hProjected :
      2 *
        inner ℝ
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q)
          (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
            hNS ht hEnd hE hTail htauR q)
        ≤
      (6 * h3PreterminalSelectedWeakStrongGradientEnvelope E) *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q‖ ^ 2 := by
    exact
      two_inner_selectedOldUnitProjectedRHSDifference_le_six_mul_norm_sq_alternate_auto
        hNS ht hEnd hE hTail htauR q

  rw [hPathDifference, hDerivativeDifference]

  exact hProjected

/-- Compatibility closure through the existing strong-path Grönwall theorem.
This remains an intermediate theorem only; the endpoint-independent weak FTC
route is intended to eliminate `hBranches`. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_projectedRHS_auto
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
    (hDerivative :
      ∀ q : Set.Icc (0 : ℝ) tau,
        hBranches.selectedDerivative (q : ℝ)
            - hBranches.oldDerivative (q : ℝ)
          =
        h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
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
      (h3PreterminalSelectedOldL2EnergyDerivativeDataOnElapsed_of_projectedRHS_auto
        hNS ht hEnd hE hTail htauR hBranches hDerivative)
      q

end

end Euclidean
end Bridge
end PrimeTensor
