import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.TailLocalWellPosedness

/-!
# Tail-aware Schwartz spectral classicalization frontier

`TailLocalWellPosedness` corrects the continuation interface by retaining the
old solution's H³ class on the overlap `[t,T)`.  The Banach-selected spectral
restart still starts from one canonical anchor state, so the only change needed
at the Schwartz classicalization layer is to keep that tail datum available
instead of discarding it after extracting the anchor slice.

This file introduces the corrected frontier:

* `CanonicalH3TailDataFrom u t T E` supplies H³ integrability and canonical
  energy `≤ E` at every old slice in `[t,T)`;
* its value at `t` canonically builds the same weighted spectral restart state
  used by the existing single-slice frontier;
* the selected path is classicalized and glued while the full tail datum
  remains in scope.

The spectral restart radius is unchanged:
`h3FinHeatLerayRestartRadius ν E`.

The main reduction proves that this tail-aware Schwartz frontier implies
`CanonicalH3RealTailLocalWellPosedness`, and therefore the original
`H3ControlProducesExtension` continuation target.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance point3MeasureSpaceH3SchwartzTailClassicalizationFrontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The tail H³ datum contains the canonical restart anchor itself. -/
theorem canonicalH3TailDataFrom_at_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t T E : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    VelocityH3IntegrableAt u t
      ∧
    velocityH3EnergyAt u t ≤ E := by
  exact
    hTail t
      ⟨
        le_rfl,
        ht.2
      ⟩

/-- Corrected selected-path classicalization frontier.

Unlike `H3SchwartzCanonicalRestartClassicalization`, this statement retains the
old solution's canonical H³ data throughout the overlap `[t,T)`.  The actual
Banach-selected restart is unchanged: its initial spectral state is the
canonical encoding of the anchor slice `u t`, and its lifespan is the same
explicit spectral radius.

The full `hTail` hypothesis remains available to the eventual overlap
uniqueness proof, preventing the local argument from forgetting the
strong-solution class of the old branch. -/
def H3SchwartzCanonicalTailRestartClassicalization
    (ν : ℝ)
    (hν : 0 < ν) : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      let hAt :
          VelocityH3IntegrableAt u t
            ∧
          velocityH3EnergyAt u t ≤ E :=
        canonicalH3TailDataFrom_at_anchor ht hTail
      let hInt : VelocityH3IntegrableAt u t :=
        hAt.1
      let hEnergy : velocityH3EnergyAt u t ≤ E :=
        hAt.2
      let hMeas : VelocityH3MeasurableAt u t :=
        velocityH3MeasurableAt_of_loggedPreterminalNavierStokes hNS ht
      let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
        velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
          hNS ht hInt
      let hEpos : 0 < E :=
        lt_of_lt_of_le zero_lt_one hE
      let U₀ : H3SpectralVelocityState :=
        velocityH3SpectralStateAt
          u t hInt hMeas hFourier
      let hU₀ : ‖U₀‖ ≤ E :=
        norm_velocityH3SpectralStateAt_le_energyCeiling
          hFourier hE hEnergy
      let R : ℝ :=
        h3FinHeatLerayRestartRadius ν E
      let W : ℝ → H3SpectralVelocityState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hEpos hU₀
      ∃
        (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
        (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
        (S : ℝ),
          t + R < S
            ∧
          RealRestartAgreesBeforeT u v T
            ∧
          PreterminalNavierStokes3 v p S
            ∧
          RealVelocitySpatialC3 v
            ∧
          RealVelocityThirdJetContinuousOn v S
            ∧
          H3SpectralRestartDecoderMatches W v t R

/-- The corrected Schwartz spectral frontier supplies tail-aware canonical
local well-posedness, with exactly the same explicit spectral restart radius. -/
theorem canonicalH3RealTailLocalWellPosedness_of_schwartzSpectralTailClassicalization
    {ν : ℝ}
    (hν : 0 < ν)
    (hClassicalize :
      H3SchwartzCanonicalTailRestartClassicalization ν hν) :
    CanonicalH3RealTailLocalWellPosedness := by
  intro E hE

  refine
    ⟨
      h3FinHeatLerayRestartRadius ν E,
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos hν hE,
      ?_
    ⟩

  intro
    u T t
    hNS
    ht
    hTail

  have hC :=
    hClassicalize
      E hE
      u T t
      hNS ht
      hTail

  dsimp only at hC

  rcases hC with
    ⟨
      v,
      p,
      S,
      hS,
      hAgree,
      hPDE,
      hSpatial,
      hThird,
      _hMatch
    ⟩

  exact
    ⟨
      v,
      p,
      S,
      hS,
      hAgree,
      hPDE,
      hSpatial,
      hThird
    ⟩

/-- The corrected Schwartz selected-path classicalization statement closes the
original H³ continuation frontier through the tail-aware local-well-posedness
reduction. -/
theorem h3ControlProducesExtension_of_schwartzSpectralTailClassicalization
    {ν : ℝ}
    (hν : 0 < ν)
    (hClassicalize :
      H3SchwartzCanonicalTailRestartClassicalization ν hν) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_tailLocalWellPosedness
      (canonicalH3RealTailLocalWellPosedness_of_schwartzSpectralTailClassicalization
        hν hClassicalize)

end
end Euclidean
end Bridge
end PrimeTensor
