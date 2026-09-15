import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.StrictOverlapWitnessFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Subinterval.Consistency

/-!
# Reduce the strict overlap-witness frontier to selected decoder agreement

A local `H3PreterminalSpectralOverlapWitnessAt` contains three pieces:

* a bounded continuous spectral path;
* the restarted mild equation;
* endpoint decoding to the old preterminal velocity.

For a positive elapsed time inside the canonical restart radius, the first two
pieces are already supplied automatically by the canonical Banach-selected
restart restricted to that shorter interval.

Therefore the only genuinely free local overlap datum is endpoint decoder
agreement of the selected restart with the old velocity.

This file packages that reduction pointwise and radius-wide, then feeds it into
the pressure-free strict-overlap endpoint theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedDecoderOverlapFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical anchor spectral state used by the selected restart. -/
noncomputable def h3PreterminalSelectedDecoderAnchorState
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

/-- The retained H³ ceiling bounds the canonical selected restart anchor. -/
theorem norm_h3PreterminalSelectedDecoderAnchorState_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    ‖h3PreterminalSelectedDecoderAnchorState hNS ht hTail‖ ≤ E := by
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
      ≤ E

  exact
    norm_velocityH3SpectralStateAt_le_energyCeiling
      hFourier
      hE
      (canonicalH3TailDataFrom_at_anchor ht hTail).2

/-- Pointwise selected-decoder agreement with the old preterminal velocity at
one positive elapsed time. -/
def H3PreterminalSelectedDecoderAgreesAt
    {ν E : ℝ}
    (hν : 0 < ν)
    (q : ℝ)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ j : Fin 3,
    ∀ᵐ x : Point3 ∂volume,
      h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν
              (h3PreterminalSelectedDecoderAnchorState
                hNS ht hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht hE hTail)
              q)
            j)
          x
        =
      (logSpaceTimeVectorField
          u
          (t + q)
          x).component
        (h3AxisOfFin3 j)

/-- At a positive time inside the canonical restart radius, selected endpoint
decoder agreement supplies the entire local overlap witness automatically. -/
theorem h3PreterminalSpectralOverlapWitnessAt_of_selectedDecoderAgreement
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hq : 0 < q)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν E)
    (hDecode :
      H3PreterminalSelectedDecoderAgreesAt
        hν q hNS ht hE hTail) :
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
      q
      hq.le := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  let P : H3SpectralPhysicalVelocityPath q :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
      hν U₀ hEpos hU₀ hq.le

  refine ⟨P, ?_, ?_, ?_⟩

  · intro r
    dsimp only [P]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical_apply_le_twoA
        hν U₀ hEpos hU₀ hq.le r

  · intro s
    dsimp only [P]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical_satisfies_mild
        hν U₀ hEpos hU₀ hq hqR s

  · intro j

    have hAE := hDecode j

    have hEndTime :
        ((h3PhysicalTimeMap q hq.le h3UnitTimeOne :
            Set.Icc (0 : ℝ) q) : ℝ)
          =
        q := by
      change h3PhysicalTime q h3UnitTimeOne = q
      exact h3PhysicalTime_one q

    change
      ∀ᵐ x : Point3 ∂volume,
        h3FromFourierRealL2
            (h3SpectralVelocityDecodeRealL2
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hEpos hU₀
                ((h3PhysicalTimeMap q hq.le h3UnitTimeOne :
                    Set.Icc (0 : ℝ) q) : ℝ))
              j)
            x
          =
        (logSpaceTimeVectorField
            u
            (t + q)
            x).component
          (h3AxisOfFin3 j)

    rw [hEndTime]

    simpa only [
      U₀,
      hEpos,
      hU₀,
      h3PreterminalSelectedDecoderAnchorState
    ] using hAE

/-- Radius-wide decoder-agreement frontier.

The only local analytic statement left is that the already-constructed
Banach-selected restart decodes to the old velocity at each positive
preterminal elapsed time. -/
def H3PreterminalSelectedDecoderAgreementOnRestartRadius
    (ν E : ℝ)
    (hν : 0 < ν)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q :
      Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν E),
    ∀ _hEnd : t + (q : ℝ) < T,
      H3PreterminalSelectedDecoderAgreesAt
        hν
        (q : ℝ)
        hNS
        ht
        hE
        hTail

/-- Radius-wide selected decoder agreement produces strict positive overlap
witnesses automatically. -/
theorem h3PreterminalStrictOverlapWitnessesOnRestartRadius_of_selectedDecoderAgreement
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hDecode :
      H3PreterminalSelectedDecoderAgreementOnRestartRadius
        ν E hν u T t hNS ht hE hTail) :
    H3PreterminalStrictOverlapWitnessesOnRestartRadius
      ν E hν u T t hNS ht hTail := by
  intro q hEnd

  exact
    h3PreterminalSpectralOverlapWitnessAt_of_selectedDecoderAgreement
      hν
      hNS
      ht
      q.property.1
      hE
      hTail
      q.property.2
      (hDecode q hEnd)

/-- Selected decoder agreement on the canonical restart radius closes the full
strong weighted-H³ spectral endpoint on every positive shorter preterminal
interval. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_selectedDecoderAgreement_pressureFree
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
    (hDecode :
      H3PreterminalSelectedDecoderAgreementOnRestartRadius
        ν E hν u T t hNS ht hE hTail) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_restartRadiusStrictOverlap_pressureFree
      hν
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      htauR
      (h3PreterminalStrictOverlapWitnessesOnRestartRadius_of_selectedDecoderAgreement
        hν
        hNS
        ht
        hE
        hTail
        hDecode)

/-- Selected decoder agreement on the canonical restart radius closes the
physical zeroth/ordered-third `L²` endpoint frontier. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_selectedDecoderAgreement_pressureFree
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
    (hDecode :
      H3PreterminalSelectedDecoderAgreementOnRestartRadius
        ν E hν u T t hNS ht hE hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_spectralState_pressureFree
      hNS
      ht
      hEnd
      hTail
      (h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_selectedDecoderAgreement_pressureFree
        hν
        hNS
        ht
        htau
        hEnd
        hE
        hTail
        htauR
        hDecode)

end

end Euclidean
end Bridge
end PrimeTensor
