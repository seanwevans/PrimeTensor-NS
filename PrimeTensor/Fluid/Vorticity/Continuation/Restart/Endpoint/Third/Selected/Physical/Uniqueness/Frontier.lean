import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Decoder.Overlap.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Pressure.Momentum

/-!
# Move the remaining overlap frontier from Fourier decoders to physical uniqueness

`SelectedDecoderOverlapFrontier` reduces the pressure-free endpoint problem to
one local statement at each positive overlap time: the canonical selected
restart's real `L²` decoder equals the old logged velocity.

The selected restart already carries a canonical smooth real physical
representative.  That representative is almost everywhere equal to the decoder.
Hence pointwise equality of the selected classical velocity and the old
classical velocity implies the decoder frontier automatically.

This file performs that final representation reduction.  The remaining problem
is now a conventional local uniqueness statement for two classical
Navier--Stokes velocities with the same restart data.  The selected branch's
pointwise momentum equation is already available from
`Selected.Pressure.Momentum`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedPhysicalUniquenessFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pointwise physical agreement of the selected classical velocity with the
old preterminal velocity at one elapsed time.

Unlike the decoder frontier, this statement contains no `L²`, Fourier, or
quotient representation layer. -/
def H3PreterminalSelectedPhysicalAgreementAt
    {ν E : ℝ}
    (hν : 0 < ν)
    (q : ℝ)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ j : Fin 3, ∀ x : Point3,
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
      hν
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht hE hTail)
      q
      x).component
        (h3AxisOfFin3 j)
      =
    (logSpaceTimeVectorField
      u
      (t + q)
      x).component
        (h3AxisOfFin3 j)

/-- Pointwise classical physical agreement implies the selected real decoder
agreement required by the strict-overlap endpoint route. -/
theorem h3PreterminalSelectedDecoderAgreesAt_of_physicalAgreement
    {ν E : ℝ}
    (hν : 0 < ν)
    (q : ℝ)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementAt
        hν q hNS ht hE hTail) :
    H3PreterminalSelectedDecoderAgreesAt
      hν q hNS ht hE hTail := by
  intro j

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  have hRepresentativeDecoder :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
      (s := q)
      hν U₀ hEpos hU₀ j

  have hSelectedDecoder :
      (fun x : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hEpos hU₀ q x).component
            (h3AxisOfFin3 j))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hEpos hU₀ q)
            j)
          x) := by
    simpa only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
    ] using hRepresentativeDecoder

  have hSelectedOld :
      (fun x : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hEpos hU₀ q x).component
            (h3AxisOfFin3 j))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (logSpaceTimeVectorField
          u
          (t + q)
          x).component
            (h3AxisOfFin3 j)) := by
    exact
      Filter.Eventually.of_forall
        (fun x => hPhysical j x)

  have hDecoderOld :=
    hSelectedDecoder.symm.trans hSelectedOld

  filter_upwards [hDecoderOld] with x hx

  simpa only [
    U₀,
    hEpos,
    hU₀,
    h3PreterminalSelectedDecoderAnchorState
  ] using hx

/-- Radius-wide physical uniqueness frontier.

At every strictly positive canonical-radius time still before the old terminal
time, the selected smooth classical velocity is exactly the old preterminal
velocity pointwise in space. -/
def H3PreterminalSelectedPhysicalAgreementOnRestartRadius
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
      H3PreterminalSelectedPhysicalAgreementAt
        hν (q : ℝ) hNS ht hE hTail

/-- Radius-wide physical uniqueness implies the selected decoder frontier. -/
theorem h3PreterminalSelectedDecoderAgreementOnRestartRadius_of_physicalAgreement
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        ν E hν u T t hNS ht hE hTail) :
    H3PreterminalSelectedDecoderAgreementOnRestartRadius
      ν E hν u T t hNS ht hE hTail := by
  intro q hEnd

  exact
    h3PreterminalSelectedDecoderAgreesAt_of_physicalAgreement
      hν
      (q : ℝ)
      hNS
      ht
      hE
      hTail
      (hPhysical q hEnd)

/-- The remaining physical uniqueness frontier closes strong weighted-H³
spectral endpoint continuity. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_selectedPhysicalAgreement_pressureFree
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
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        ν E hν u T t hNS ht hE hTail) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_selectedDecoderAgreement_pressureFree
      hν
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      htauR
      (h3PreterminalSelectedDecoderAgreementOnRestartRadius_of_physicalAgreement
        hν
        hNS
        ht
        hE
        hTail
        hPhysical)

/-- The remaining physical uniqueness frontier closes the concrete physical
zeroth/ordered-third `L²` endpoint continuity used by the restart machinery. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_selectedPhysicalAgreement_pressureFree
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
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        ν E hν u T t hNS ht hE hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_spectralState_pressureFree
      hNS
      ht
      hEnd
      hTail
      (h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_selectedPhysicalAgreement_pressureFree
        hν
        hNS
        ht
        htau
        hEnd
        hE
        hTail
        htauR
        hPhysical)

/-- The selected branch already satisfies the ordinary unit-viscosity momentum
equation at every strict positive interior restart time.

This records that the selected half of the remaining physical uniqueness
problem is already discharged; no new PDE identity is assumed by the physical
agreement frontier above. -/
theorem h3PreterminalSelectedPhysicalBranch_unitViscosityMomentum
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs0 : 0 < s)
    (hsR :
      s < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    temporal.d
        (fun τ : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W τ i) x)
        s
      +
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (h3SpectralRealVelocityOfPath W)
      s x).component
        (h3AxisOfFin3 i)
      =
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3RawFinPressureRealC1OfPath W)
        s x
        (h3AxisOfFin3 i)
      +
    (∑ j : Fin 3,
      spatial3.d
        (h3AxisOfFin3 j)
        (spatial3.d
          (h3AxisOfFin3 j)
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s i)))
        x) := by
  simpa only [one_mul] using
    h3PreterminalTailCanonicalSelectedRestart_pressure_momentum_fin
      (one_pos : (0 : ℝ) < 1)
      hNS
      ht
      hE
      hTail
      hs0
      hsR
      i
      x

end

end Euclidean
end Bridge
end PrimeTensor
