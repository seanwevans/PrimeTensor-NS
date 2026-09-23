import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedPhysicalL2EnergyGermBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.StrictOverlapSpectralEquality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongRHSDifference

/-!
# Selected restart: exact spectral equality with the old overlap slice

The selected physical kinetic-energy derivative has now been transported to
the canonical old zeroth-order energy.  The remaining coefficient comparison
involves the selected projected RHS.

Before comparing those RHS vectors, remove the last state-level representation
seam.  Pointwise selected/old physical agreement implies selected decoder
agreement.  The existing decoder-overlap construction upgrades that to a local
spectral overlap witness, and strict-overlap decoder injectivity then identifies
the complete weighted H³ spectral states.

Thus, at every positive elapsed overlap point,

    U_selected(q) = U_old(q)

exactly in `H3SpectralVelocityState`.

This is stronger than the physical `L²` energy equality and lets subsequent
increments rewrite the selected Laplacian and nonlinear forcing directly to
their old-snapshot spectral counterparts.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedSpectralStateOldBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pointwise selected/old physical agreement at a positive elapsed point
upgrades to exact equality of the selected weighted H³ state and the canonical
old weighted H³ snapshot at that point. -/
theorem h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_physicalAgreement
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
    (q : Set.Icc (0 : ℝ) tau)
    (hq : 0 < (q : ℝ))
    (hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        (q : ℝ)
        hNS ht hE hTail) :
    h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)
      =
    h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q := by
  have hqR :
      (q : ℝ) ≤
        h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    q.property.2.trans htauR

  have hDecode :
      H3PreterminalSelectedDecoderAgreesAt
        (one_pos : (0 : ℝ) < 1)
        (q : ℝ)
        hNS ht hE hTail :=
    h3PreterminalSelectedDecoderAgreesAt_of_physicalAgreement
      (one_pos : (0 : ℝ) < 1)
      (q : ℝ)
      hNS ht hE hTail
      hAgreement

  have hWitness :
      H3PreterminalSpectralOverlapWitnessAt
        (1 : ℝ)
        E
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1)
        u
        t
        (q : ℝ)
        q.property.1 :=
    h3PreterminalSpectralOverlapWitnessAt_of_selectedDecoderAgreement
      (one_pos : (0 : ℝ) < 1)
      hNS
      ht
      hq
      hE
      hTail
      hqR
      hDecode

  have hState :
      h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_velocityH3SpectralStateAt_le_energyCeiling
          (velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
            hNS
            ht
            (canonicalH3TailDataFrom_at_anchor ht hTail).1)
          hE
          (canonicalH3TailDataFrom_at_anchor ht hTail).2)
        (q : ℝ) :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed_eq_selected_of_overlapWitness
      (one_pos : (0 : ℝ) < 1)
      hNS
      ht
      hEnd
      hE
      hTail
      q
      hq
      hqR
      hWitness

  symm

  simpa only [
    h3PreterminalSelectedUnitSpectralStateOnRadius,
    h3PreterminalElapsedToSelectedUnitRadius_coe,
    h3PreterminalSelectedDecoderAnchorState
  ] using hState

/-- Radius-wide physical agreement supplies exact selected/old spectral equality
at every positive closed elapsed point that remains before the old terminal
time. -/
theorem h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_restartRadiusAgreement
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
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (hq : 0 < (q : ℝ)) :
    h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)
      =
    h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q := by
  let qR :
      Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨
      (q : ℝ),
      hq,
      q.property.2.trans htauR
    ⟩

  have hEndq :
      t + (qR : ℝ) < T := by
    dsimp only [qR]
    linarith [q.property.2, hEnd]

  have hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        (q : ℝ)
        hNS ht hE hTail := by
    simpa only [qR] using
      hPhysical qR hEndq

  exact
    h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_physicalAgreement
      hNS ht hEnd hE hTail htauR q hq hAgreement

end

end Euclidean
end Bridge
end PrimeTensor
