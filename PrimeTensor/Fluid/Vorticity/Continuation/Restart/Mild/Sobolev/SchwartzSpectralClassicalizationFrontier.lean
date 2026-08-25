import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralPreterminalCanonicalEnergyRestartClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.LocalWellPosedness

/-!
# Classicalization frontier for the canonical spectral H³ restart

The spectral restart construction is now available from exactly the snapshot
hypotheses used by the canonical real H³ continuation interface.  It also
carries exact real realizability and the Schwartz physical Duhamel closure.

What remains is a genuinely classical PDE statement: the selected real-decoded
mild path must admit a pointwise spacetime representative which is spatially
`C³`, has the required time/mixed regularity, satisfies Navier--Stokes with a
pressure, and glues to the old preterminal solution.

This file isolates that final analytic statement without weakening it.  The
matching predicate below requires the classical representative to agree almost
everywhere, componentwise, with the canonical real `L²` decoder of the actual
Banach-selected spectral path on the restart interval.

The main reduction theorem then shows that this single classicalization input
implies the existing `CanonicalH3RealLocalWellPosedness` interface, hence the
uniform canonical lifespan and the H³ continuation frontier already proved in
the restart stack.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance point3MeasureSpaceH3SchwartzClassicalizationFrontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A real spacetime field represents the canonical real decoder of a spectral
restart path on a physical interval, componentwise and almost everywhere in
space. -/
def H3SpectralRestartDecoderMatches
    (W : ℝ → H3SpectralVelocityState)
    (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t R : ℝ) : Prop :=
  ∀ (q : Set.Icc (0 : ℝ) R) (j : Fin 3),
    ∀ᵐ x : Point3 ∂volume,
      h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2 (W (q : ℝ)) j) x
        =
      (v (t + (q : ℝ)) x).component (h3AxisOfFin3 j)

/--
The exact remaining analytic input for the canonical spectral restart.

For every canonical H³ energy ceiling and every admissible interior restart
slice, classicalize the *specific Banach-selected restart path* produced by the
spectral construction.  Besides the classical restart properties required by
the old continuation interface, the resulting velocity must match the
canonical real decoder of that selected path throughout the restart window.
-/
def H3SchwartzCanonicalRestartClassicalization
    (ν : ℝ)
    (hν : 0 < ν) : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t)
    (hEnergy : velocityH3EnergyAt u t ≤ E),
      let hMeas : VelocityH3MeasurableAt u t :=
        velocityH3MeasurableAt_of_loggedPreterminalNavierStokes hNS ht
      let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
        velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
          hNS ht hInt
      let hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
      let U₀ : H3SpectralVelocityState :=
        velocityH3SpectralStateAt u t hInt hMeas hFourier
      let hU₀ : ‖U₀‖ ≤ E :=
        norm_velocityH3SpectralStateAt_le_energyCeiling
          hFourier hE hEnergy
      let R : ℝ := h3FinHeatLerayRestartRadius ν E
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

/-- The classicalization frontier immediately supplies the per-energy real
local-well-posedness interface, with the canonical spectral restart radius as
its uniform window. -/
theorem canonicalH3RealLocalWellPosedness_of_schwartzSpectralClassicalization
    {ν : ℝ}
    (hν : 0 < ν)
    (hClassicalize : H3SchwartzCanonicalRestartClassicalization ν hν) :
    CanonicalH3RealLocalWellPosedness := by
  intro E hE

  refine
    ⟨
      h3FinHeatLerayRestartRadius ν E,
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos hν hE,
      ?_
    ⟩

  intro u T t hNS ht hInt hEnergy

  have hC :=
    hClassicalize
      E hE u T t hNS ht hInt hEnergy

  dsimp only at hC

  rcases hC with
    ⟨v, p, S, hS, hAgree, hPDE, hSpatial, hThird, _hMatch⟩

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

/-- The same concrete classicalization input therefore supplies the existing
uniform canonical H³ restart lifespan. -/
theorem uniformCanonicalH3RealRestartLifespan_of_schwartzSpectralClassicalization
    {ν : ℝ}
    (hν : 0 < ν)
    (hClassicalize : H3SchwartzCanonicalRestartClassicalization ν hν) :
    UniformCanonicalH3RealRestartLifespan := by
  exact
    uniformCanonicalH3RealRestartLifespan_of_localWellPosedness
      (canonicalH3RealLocalWellPosedness_of_schwartzSpectralClassicalization
        hν hClassicalize)

/-- Consequently, proving the selected-path classicalization statement closes
the already-isolated H³ continuation frontier. -/
theorem h3ControlProducesExtension_of_schwartzSpectralClassicalization
    {ν : ℝ}
    (hν : 0 < ν)
    (hClassicalize : H3SchwartzCanonicalRestartClassicalization ν hν) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_localWellPosedness
      (canonicalH3RealLocalWellPosedness_of_schwartzSpectralClassicalization
        hν hClassicalize)

end

end Euclidean
end Bridge
end PrimeTensor
