import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel
import Mathlib.Tactic.FinCases

/-!
# Global resolved physical PDE envelope

The resolved terminal obstruction has four physical channels for each of the
three velocity coordinates.  This file packages them into one scalar envelope.

For a fixed coordinate, take the maximum of

* `‖d/dt(q û_j)‖²`,
* the full physical top H³ dissipation,
* `‖d/dt(q² û_j)‖²`,
* `‖q³ û_j‖²`.

Then take the maximum over coordinates `0,1,2`.

Every resolved channel amplitude is pointwise bounded above by this global
envelope.  Therefore the already-frozen fixed-channel obstruction implies that
hypothetical nonextension makes this one scalar envelope cofinally unbounded
on every strict terminal tail.

Conversely, boundedness of the envelope on one strict terminal tail forces
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalResolvedPhysicalPDEEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 900000

/-! ## Coordinate and global envelopes -/

/--
Maximum of the four resolved physical PDE channel amplitudes for one fixed
velocity coordinate.
-/
noncomputable def h3TerminalResolvedPhysicalPDECoordinateEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    ℝ :=
  max
    (h3TerminalResolvedPhysicalPDEChannelAmplitude
      hH3 hClass j
      H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
      t)
    (max
      (h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.topDissipation
        t)
      (max
        (h3TerminalResolvedPhysicalPDEChannelAmplitude
          hH3 hClass j
          H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
          t)
        (h3TerminalResolvedPhysicalPDEChannelAmplitude
          hH3 hClass j
          H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
          t)))

/--
Every named resolved channel is bounded by the coordinate envelope.
-/
theorem h3TerminalResolvedPhysicalPDEChannelAmplitude_le_coordinateEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (t : ℝ) :
    h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass j channel t
      ≤
    h3TerminalResolvedPhysicalPDECoordinateEnvelope
      hH3 hClass j t := by

  unfold h3TerminalResolvedPhysicalPDECoordinateEnvelope

  cases channel with

  | lowerTemporal =>
      exact
        le_max_left _ _

  | topDissipation =>
      exact
        le_trans
          (le_max_left _ _)
          (le_max_right _ _)

  | fourthTemporal =>
      exact
        le_trans
          (le_max_left _ _)
          (
            le_trans
              (le_max_right _ _)
              (le_max_right _ _)
          )

  | sixthDiffusion =>
      exact
        le_trans
          (le_max_right _ _)
          (
            le_trans
              (le_max_right _ _)
              (le_max_right _ _)
          )

/--
Single scalar envelope over all four resolved channels and all three velocity
coordinates.
-/
noncomputable def h3TerminalResolvedPhysicalPDEEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) :
    ℝ :=
  max
    (h3TerminalResolvedPhysicalPDECoordinateEnvelope
      hH3 hClass (0 : Fin 3) t)
    (max
      (h3TerminalResolvedPhysicalPDECoordinateEnvelope
        hH3 hClass (1 : Fin 3) t)
      (h3TerminalResolvedPhysicalPDECoordinateEnvelope
        hH3 hClass (2 : Fin 3) t))

/--
Every coordinate envelope is bounded by the single global envelope.
-/
theorem h3TerminalResolvedPhysicalPDECoordinateEnvelope_le_envelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    h3TerminalResolvedPhysicalPDECoordinateEnvelope
        hH3 hClass j t
      ≤
    h3TerminalResolvedPhysicalPDEEnvelope
      hH3 hClass t := by

  unfold h3TerminalResolvedPhysicalPDEEnvelope

  fin_cases j

  · exact
      le_max_left _ _

  · exact
      le_trans
        (le_max_left _ _)
        (le_max_right _ _)

  · exact
      le_trans
        (le_max_right _ _)
        (le_max_right _ _)

/--
Every individual resolved channel amplitude is pointwise bounded by the global
resolved PDE envelope.
-/
theorem h3TerminalResolvedPhysicalPDEChannelAmplitude_le_envelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (t : ℝ) :
    h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass j channel t
      ≤
    h3TerminalResolvedPhysicalPDEEnvelope
      hH3 hClass t := by

  exact
    (
      h3TerminalResolvedPhysicalPDEChannelAmplitude_le_coordinateEnvelope
        hH3 hClass j channel t
    ).trans
      (
        h3TerminalResolvedPhysicalPDECoordinateEnvelope_le_envelope
          hH3 hClass j t
      )

/-! ## Intrinsic scalar obstruction -/

/--
The single resolved physical PDE envelope is cofinally unbounded at `T`.
-/
def H3TerminalResolvedPhysicalPDEEnvelopeCofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Prop :=
  ∀ c : ℝ,
    c ∈ Set.Ioo a T →
    ∀ M : ℝ,
      ∃ t : ℝ,
        t ∈ Set.Ioo c T
          ∧
        M
          <
        h3TerminalResolvedPhysicalPDEEnvelope
          hH3 hClass t

/--
Cofinal escape of any one fixed resolved channel implies cofinal escape of the
global scalar envelope.
-/
theorem resolvedPhysicalPDEEnvelope_cofinallyUnbounded_of_channel_cofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (hChannel :
      H3TerminalResolvedPhysicalPDEChannelCofinallyUnbounded
        hH3 hClass j channel) :
    H3TerminalResolvedPhysicalPDEEnvelopeCofinallyUnbounded
      hH3 hClass := by

  intro c hc M

  obtain
    ⟨t, htTail, hLarge⟩ :=
    hChannel c hc M

  exact
    ⟨
      t,
      htTail,
      lt_of_lt_of_le
        hLarge
        (
          h3TerminalResolvedPhysicalPDEChannelAmplitude_le_envelope
            hH3 hClass j channel t
        )
    ⟩

/--
Under the retained endpoint hypotheses, hypothetical nonextension forces the
single global resolved physical PDE envelope to be cofinally unbounded on
every strict terminal tail.
-/
theorem resolvedPhysicalPDEEnvelope_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T) :
    H3TerminalResolvedPhysicalPDEEnvelopeCofinallyUnbounded
      hH3 hClass := by

  obtain
    ⟨j₀, channel, hChannel⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  exact
    resolvedPhysicalPDEEnvelope_cofinallyUnbounded_of_channel_cofinallyUnbounded
      hH3 hClass j₀ channel hChannel

/--
Neutral scalar endpoint formulation.

Either the path extends smoothly through `T`, or the one global resolved
physical PDE envelope is cofinally unbounded on every strict terminal tail.
-/
theorem smoothContinuationExtension_or_resolvedPhysicalPDEEnvelope_cofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    H3TerminalResolvedPhysicalPDEEnvelopeCofinallyUnbounded
      hH3 hClass := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (
          resolvedPhysicalPDEEnvelope_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

/-! ## Scalar continuation criterion -/

/--
If the global resolved physical PDE envelope is bounded on one strict terminal
tail, then the H³ path extends smoothly through the terminal time.
-/
theorem smoothContinuationExtension_of_resolvedPhysicalPDEEnvelope_bounded_on_terminalTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hBounded :
      ∃ c : ℝ,
        c ∈ Set.Ioo a T
          ∧
        ∃ M : ℝ,
          ∀ t : ℝ,
            t ∈ Set.Ioo c T →
            h3TerminalResolvedPhysicalPDEEnvelope
                hH3 hClass t
              ≤
            M) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  classical

  by_contra hNoExtension

  have hCofinal :=
    resolvedPhysicalPDEEnvelope_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  obtain
    ⟨c, hc, M, hBound⟩ :=
    hBounded

  obtain
    ⟨t, htTail, hLarge⟩ :=
    hCofinal c hc M

  exact
    (not_lt_of_ge
      (hBound t htTail))
      hLarge

end

end Euclidean
end Bridge
end PrimeTensor
