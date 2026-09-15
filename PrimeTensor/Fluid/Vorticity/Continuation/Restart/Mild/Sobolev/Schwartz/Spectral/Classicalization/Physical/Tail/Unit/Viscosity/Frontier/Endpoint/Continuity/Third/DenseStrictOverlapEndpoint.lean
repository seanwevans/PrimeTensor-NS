import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.StrictOverlapSpectralEquality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Physical.Realization

/-!
# Endpoint continuity from dense strict old/selected overlap

The previous two checkpoints isolate a second route to the old-branch endpoint:

* pressure-free weak continuity plus dense agreement with a strongly continuous
  comparison path extends the agreement to the closed endpoint;
* every positive local overlap witness already gives exact equality of the old
  canonical weighted H³ spectral state and the selected mild state.

This file composes those facts.

No scalar H³ energy continuity, higher mixed-time derivative, dominated
differentiation, or endpoint continuity is assumed here.  The remaining local
analytic input is only a dense family of genuine positive overlap witnesses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3DenseStrictOverlapEndpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A dense family of strict positive local overlap witnesses closes the full
weighted-H³ spectral endpoint continuously.

The dense parameter set is deliberately abstract.  A later analytic theorem
may instantiate it by rational elapsed times, a canonical sequence, or all
strict positive elapsed times. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_denseStrictOverlapWitnesses_pressureFree
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
    {D : Type*}
    (ι : D → Set.Icc (0 : ℝ) tau)
    (hDense : DenseRange ι)
    (hPositive :
      ∀ d : D, 0 < ((ι d : Set.Icc (0 : ℝ) tau) : ℝ))
    (hWitness :
      ∀ d : D,
        H3PreterminalSpectralOverlapWitnessAt
          ν
          E
          hν
          (h3PreterminalCanonicalAnchorSpectralState
            hNS
            ht
            (canonicalH3TailDataFrom_at_anchor ht hTail).1)
          u
          t
          ((ι d : Set.Icc (0 : ℝ) tau) : ℝ)
          (ι d).property.1) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  let hInt0 : VelocityH3IntegrableAt u t :=
    (canonicalH3TailDataFrom_at_anchor ht hTail).1

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalCanonicalAnchorSpectralState
      hNS ht hInt0

  have hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ :
      ‖U₀‖ ≤ E := by
    let hMeas0 : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hNS ht

    let hFourier0 :
        VelocityH3FourierCompatibleAt
          u t hInt0 hMeas0 :=
      velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
        hNS ht hInt0

    change
      ‖velocityH3SpectralStateAt
          u t hInt0 hMeas0 hFourier0‖
        ≤ E

    exact
      norm_velocityH3SpectralStateAt_le_energyCeiling
        hFourier0
        hE
        (canonicalH3TailDataFrom_at_anchor ht hTail).2

  let G :
      Set.Icc (0 : ℝ) tau →
        H3SpectralVelocityState :=
    fun q =>
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hEpos hU₀ (q : ℝ)

  have hSelectedGlobal :
      Continuous
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hEpos hU₀) := by
    have hC :=
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
        hν
        (h3FinHeatLerayRestartRadius_pos ν hEpos).le
        U₀
        hEpos
        hU₀
        (h3FinHeatLerayRestartRadius_smallness ν hEpos.le)

    simpa only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hC.1

  have hG : Continuous G := by
    exact
      hSelectedGlobal.comp continuous_subtype_val

  have hEq :
      ∀ d : D,
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail (ι d)
          =
        G (ι d) := by
    intro d

    have hqR :
        ((ι d : Set.Icc (0 : ℝ) tau) : ℝ)
          ≤
        h3FinHeatLerayRestartRadius ν E :=
      le_trans (ι d).property.2 htauR

    have hStrict :=
      h3PreterminalTailCanonicalSpectralStateOnElapsed_eq_selected_of_overlapWitness
        hν
        hNS
        ht
        hEnd
        hE
        hTail
        (ι d)
        (hPositive d)
        hqR
        (hWitness d)

    simpa only [
      G,
      U₀,
      hInt0
    ] using hStrict

  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_denseStrongAgreement_pressureFree
      hNS
      ht
      hEnd
      hE
      hTail
      G
      ι
      hDense
      hG
      hEq

/-- The same dense strict-overlap hypothesis gives precisely the physical
zeroth/ordered-third `L²` endpoint continuity consumed by the old overlap
machinery. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_denseStrictOverlapWitnesses_pressureFree
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
    {D : Type*}
    (ι : D → Set.Icc (0 : ℝ) tau)
    (hDense : DenseRange ι)
    (hPositive :
      ∀ d : D, 0 < ((ι d : Set.Icc (0 : ℝ) tau) : ℝ))
    (hWitness :
      ∀ d : D,
        H3PreterminalSpectralOverlapWitnessAt
          ν
          E
          hν
          (h3PreterminalCanonicalAnchorSpectralState
            hNS
            ht
            (canonicalH3TailDataFrom_at_anchor ht hTail).1)
          u
          t
          ((ι d : Set.Icc (0 : ℝ) tau) : ℝ)
          (ι d).property.1) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_spectralState_pressureFree
      hNS
      ht
      hEnd
      hTail
      (h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_denseStrictOverlapWitnesses_pressureFree
        hν
        hNS
        ht
        htau
        hEnd
        hE
        hTail
        htauR
        ι
        hDense
        hPositive
        hWitness)

end

end Euclidean
end Bridge
end PrimeTensor
