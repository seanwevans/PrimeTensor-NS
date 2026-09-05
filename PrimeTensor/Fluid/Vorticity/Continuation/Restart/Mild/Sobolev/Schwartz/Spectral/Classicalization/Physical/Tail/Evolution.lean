import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Path

/-!
# Classicalization: radius-wide physical tail evolution

`PhysicalTailEndpointCanonicalPath` reduces one local preterminal overlap witness
to exactly two honest analytic inputs:

1. strong continuity of only the physical zeroth and ordered third H³ `L²` jets;
2. the restarted heat--Leray mild identity.

First- and second-order physical jet continuity are no longer independent
requirements of the old-branch evolution frontier.

This file packages the two surviving inputs over the entire canonical restart
radius.

The resulting proposition is the current old-branch evolution frontier.  It
does not hide either analytic requirement, and it does not identify the
normalized preterminal PDE with an arbitrary viscosity parameter.

From the radius-wide evolution proposition we prove that the Banach-selected
spectral restart agrees, through its canonical real decoder, with the old
preterminal solution at every time in the genuine overlap.  All local path
construction and uniqueness bookkeeping are discharged by the already-green
overlap machinery.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalTailEvolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical spectral restart anchor coming from the retained H³ tail. -/
noncomputable def h3PreterminalTailCanonicalAnchorSpectralState
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3SpectralVelocityState :=
  h3PreterminalCanonicalAnchorSpectralState
    hNS
    ht
    (canonicalH3TailDataFrom_at_anchor ht hTail).1

/-- The retained canonical energy ceiling bounds the canonical anchor spectral
norm. -/
theorem norm_h3PreterminalTailCanonicalAnchorSpectralState_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    ‖h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail‖
      ≤
    E := by
  let hInt : VelocityH3IntegrableAt u t :=
    (canonicalH3TailDataFrom_at_anchor ht hTail).1

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS ht

  let hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt

  change
    ‖velocityH3SpectralStateAt
        u t hInt hMeas hFourier‖
      ≤
    E

  exact
    norm_velocityH3SpectralStateAt_le_energyCeiling
      hFourier
      hE
      (canonicalH3TailDataFrom_at_anchor ht hTail).2

/-- The canonical Banach-selected spectral restart launched from the retained
tail anchor. -/
noncomputable def h3PreterminalTailCanonicalSelectedRestart
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    ℝ → H3SpectralVelocityState :=
  h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    hν
    (h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail)
    (lt_of_lt_of_le zero_lt_one hE)
    (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail)

/-- At one positive overlap length `τ`, the old branch has the two physical
evolution properties needed to become a spectral overlap witness.

The continuity witness is now endpoint-only: zeroth and ordered third physical
H³ `L²` jets. -/
def H3PreterminalTailPhysicalEvolutionAt
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hτ : 0 ≤ τ)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∃ hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail,
    ∀ s : H3UnitTime,
      h3SpectralVelocityHeatApplyNN
          ν hν.le
          (h3PhysicalTimeNN τ hτ s)
          (h3PreterminalCanonicalAnchorSpectralState
            hNS
            ht
            (canonicalH3TailDataFrom_at_anchor
              ht hTail).1)
        -
      h3SpectralFinHeatLerayDuhamel
          ν
          (h3PhysicalTime τ s)
          hν
          (h3PathPhysicalRealExtension
            τ
            (h3SpectralNormalizedPathOfPhysical
              hτ
              (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
                hNS ht hEnd hE hTail hEndpoint)))
          (h3PathPhysicalRealExtension
            τ
            (h3SpectralNormalizedPathOfPhysical
              hτ
              (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
                hNS ht hEnd hE hTail hEndpoint)))
        =
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint
        (h3PhysicalTimeMap τ hτ s)

/-- Radius-wide physical evolution of the old H³ tail.

Only positive elapsed times need a local evolution witness; elapsed time zero
is handled by the exact encoder/decoder round trip in the selected-overlap
theorem. -/
def H3PreterminalTailPhysicalEvolutionOnRestartRadius
    (ν E : ℝ)
    (hν : 0 < ν)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius ν E),
    0 < (q : ℝ) →
    ∀ hEnd : t + (q : ℝ) < T,
      H3PreterminalTailPhysicalEvolutionAt
        hν
        hNS
        ht
        q.property.1
        hEnd
        hE
        hTail

/-- One local physical evolution package produces the corresponding local
spectral overlap witness. -/
theorem h3PreterminalSpectralOverlapWitnessAt_of_tailPhysicalEvolutionAt
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hτ : 0 ≤ τ)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionAt
        hν hNS ht hτ hEnd hE hTail) :
    H3PreterminalSpectralOverlapWitnessAt
      ν
      E
      hν
      (h3PreterminalCanonicalAnchorSpectralState
        hNS
        ht
        (canonicalH3TailDataFrom_at_anchor
          ht hTail).1)
      u
      t
      τ
      hτ := by
  rcases hEvolution with
    ⟨hEndpoint, hMild⟩

  exact
    h3PreterminalSpectralOverlapWitnessAt_of_tailL2EndpointCanonicalPath
      hν
      hNS
      ht
      hτ
      hEnd
      hE
      hTail
      hEndpoint
      hMild

/-- Radius-wide physical evolution implies exact decoder agreement between the
canonical selected restart and the old preterminal branch on their genuine
overlap. -/
theorem h3PreterminalTailCanonicalSelectedRestart_decoderAgreesOnOverlap
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail) :
    H3SelectedRestartDecoderAgreesWithPreterminalOnOverlap
      (h3PreterminalTailCanonicalSelectedRestart
        hν hNS ht hE hTail)
      u
      t
      T
      (h3FinHeatLerayRestartRadius ν E) := by
  let hInt : VelocityH3IntegrableAt u t :=
    (canonicalH3TailDataFrom_at_anchor ht hTail).1

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS ht

  let hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt

  let U₀ : H3SpectralVelocityState :=
    velocityH3SpectralStateAt
      u t hInt hMeas hFourier

  have hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ : ‖U₀‖ ≤ E := by
    exact
      norm_velocityH3SpectralStateAt_le_energyCeiling
        hFourier
        hE
        (canonicalH3TailDataFrom_at_anchor ht hTail).2

  have hOverlap :
      H3SelectedRestartDecoderAgreesWithPreterminalOnOverlap
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hEpos hU₀)
        u
        t
        T
        (h3FinHeatLerayRestartRadius ν E) := by
    apply
      h3SelectedRestartDecoderAgreesWithPreterminalOnOverlap_of_witnesses
        hν
        u
        hInt
        hMeas
        hFourier
        hEpos
        hU₀

    intro q hqPos hBefore

    have hLocal :=
      hEvolution q hqPos hBefore

    exact
      h3PreterminalSpectralOverlapWitnessAt_of_tailPhysicalEvolutionAt
        hν
        hNS
        ht
        q.property.1
        hBefore
        hE
        hTail
        hLocal

  have hSelectedEq :
      h3PreterminalTailCanonicalSelectedRestart
          hν hNS ht hE hTail
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hEpos hU₀ := by
    unfold h3PreterminalTailCanonicalSelectedRestart
    unfold h3PreterminalTailCanonicalAnchorSpectralState
    unfold h3PreterminalCanonicalAnchorSpectralState
    dsimp only

  rw [hSelectedEq]

  exact hOverlap

end
end Euclidean
end Bridge
end PrimeTensor
