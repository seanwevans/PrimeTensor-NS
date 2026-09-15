import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.DenseStrictOverlapEndpoint

/-!
# Replace abstract dense overlap data by all strict positive overlap times

`DenseStrictOverlapEndpoint` deliberately accepted an arbitrary dense parameter
family.  For the continuation problem the natural dense family is canonical:

    (0, τ] ⊆ [0, τ].

For `τ > 0`, Mathlib's `closure_Ioc` says that `(0,τ]` is dense in `[0,τ]`.
Thus it is enough to have a local spectral overlap witness at every strictly
positive elapsed time.

This file packages that noncircular frontier both on one elapsed interval and
uniformly across the canonical restart radius.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3StrictOverlapWitnessFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Strictly positive elapsed times are dense in the closed elapsed interval. -/
theorem denseRange_h3StrictPositiveElapsedInclusion
    {tau : ℝ}
    (htau : 0 < tau) :
    DenseRange
      (Set.inclusion
        (Ioc_subset_Icc_self :
          Set.Ioc (0 : ℝ) tau ⊆ Set.Icc (0 : ℝ) tau)) := by
  rw [denseRange_inclusion_iff]
  rw [closure_Ioc (ne_of_lt htau)]

/-- Local noncircular overlap frontier: every strictly positive elapsed time
has an old/selected spectral overlap witness. -/
def H3PreterminalStrictOverlapWitnessesOnElapsed
    {ν E : ℝ}
    (hν : 0 < ν)
    (tau : ℝ)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Ioc (0 : ℝ) tau,
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
      (q : ℝ)
      q.property.1.le

/-- Witnesses at every positive elapsed time automatically instantiate the
abstract dense-family endpoint theorem. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_strictOverlapWitnesses_pressureFree
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
    (hWitness :
      H3PreterminalStrictOverlapWitnessesOnElapsed
        hν tau hNS ht hTail) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  let ι :
      Set.Ioc (0 : ℝ) tau →
        Set.Icc (0 : ℝ) tau :=
    Set.inclusion Ioc_subset_Icc_self

  have hDense : DenseRange ι := by
    dsimp only [ι]
    exact
      denseRange_h3StrictPositiveElapsedInclusion htau

  have hPositive :
      ∀ d : Set.Ioc (0 : ℝ) tau,
        0 < ((ι d : Set.Icc (0 : ℝ) tau) : ℝ) := by
    intro d
    exact d.property.1

  have hLocal :
      ∀ d : Set.Ioc (0 : ℝ) tau,
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
          (ι d).property.1 := by
    intro d
    exact hWitness d

  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_denseStrictOverlapWitnesses_pressureFree
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
      hLocal

/-- Physical endpoint continuity from witnesses at every positive elapsed time. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_strictOverlapWitnesses_pressureFree
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
    (hWitness :
      H3PreterminalStrictOverlapWitnessesOnElapsed
        hν tau hNS ht hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_spectralState_pressureFree
      hNS
      ht
      hEnd
      hTail
      (h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_strictOverlapWitnesses_pressureFree
        hν
        hNS
        ht
        htau
        hEnd
        hE
        hTail
        htauR
        hWitness)

/-- Radius-wide noncircular strict-overlap frontier.

Unlike `H3PreterminalTailPhysicalEvolutionOnRestartRadius`, this proposition
contains no endpoint-continuity field.  It asks only for the actual local
old/selected overlap witness at every positive canonical-radius time that still
lies before the old terminal time. -/
def H3PreterminalStrictOverlapWitnessesOnRestartRadius
    (ν E : ℝ)
    (hν : 0 < ν)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q :
      Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν E),
    ∀ hEnd : t + (q : ℝ) < T,
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
        (q : ℝ)
        q.property.1.le

/-- Restrict radius-wide strict-overlap witnesses to any positive shorter
elapsed interval. -/
theorem h3PreterminalStrictOverlapWitnessesOnElapsed_of_restartRadius
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius ν E)
    (hRadius :
      H3PreterminalStrictOverlapWitnessesOnRestartRadius
        ν E hν u T t hNS ht hTail) :
    H3PreterminalStrictOverlapWitnessesOnElapsed
      hν tau hNS ht hTail := by
  intro q

  let qR :
      Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν E) :=
    ⟨(q : ℝ),
      q.property.1,
      le_trans q.property.2 htauR⟩

  have hqEnd :
      t + (q : ℝ) < T := by
    linarith [q.property.2, hEnd]

  have hLocal :=
    hRadius qR hqEnd

  simpa only [qR] using hLocal

/-- Radius-wide strict overlap closes weighted-H³ spectral continuity on every
positive shorter preterminal interval. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_restartRadiusStrictOverlap_pressureFree
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
    (hRadius :
      H3PreterminalStrictOverlapWitnessesOnRestartRadius
        ν E hν u T t hNS ht hTail) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_strictOverlapWitnesses_pressureFree
      hν
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      htauR
      (h3PreterminalStrictOverlapWitnessesOnElapsed_of_restartRadius
        hν
        hNS
        ht
        htau
        hEnd
        hTail
        htauR
        hRadius)

/-- Radius-wide strict overlap closes the physical zeroth/ordered-third endpoint
continuity frontier on every positive shorter preterminal interval. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_restartRadiusStrictOverlap_pressureFree
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
    (hRadius :
      H3PreterminalStrictOverlapWitnessesOnRestartRadius
        ν E hν u T t hNS ht hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_spectralState_pressureFree
      hNS
      ht
      hEnd
      hTail
      (h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_restartRadiusStrictOverlap_pressureFree
        hν
        hNS
        ht
        htau
        hEnd
        hE
        hTail
        htauR
        hRadius)

end

end Euclidean
end Bridge
end PrimeTensor
