import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure

/-!
# Canonical resolved physical PDE channel

The lower weighted derivative is now closed, so the terminal obstruction has
four genuine physical channels and no auxiliary forcing branch:

* lower temporal: `‖d/dt(q û_j)‖²`;
* top dissipation: the full physical H³ dissipation block;
* fourth temporal: `‖d/dt(q² û_j)‖²`;
* sixth diffusion: `‖q³ û_j‖²`.

This file packages those four outcomes as one finite named channel and one
scalar amplitude.  The previous nested disjunction is thereby replaced by a
single intrinsic statement:

    under hypothetical nonextension,
    one fixed coordinate and one fixed physical PDE channel
    is cofinally unbounded on every strict terminal tail.

No new analytic estimate is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalResolvedPhysicalPDEChannel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 800000

/--
The four resolved physical terminal PDE channels.
-/
inductive H3TerminalResolvedPhysicalPDEChannel where
  | lowerTemporal
  | topDissipation
  | fourthTemporal
  | sixthDiffusion
  deriving DecidableEq, Repr

/--
Scalar amplitude attached to one resolved physical PDE channel.

The coordinate argument is retained uniformly even though the full top
dissipation channel itself is coordinate-independent.
-/
noncomputable def h3TerminalResolvedPhysicalPDEChannelAmplitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (t : ℝ) :
    ℝ :=
  match channel with
  | .lowerTemporal =>
      (
        ‖deriv
            (h3TerminalPhysicalLowerWeightedVelocityFourierL2Path
              hH3 hClass j)
            t‖ : ℝ
      ) ^ 2
  | .topDissipation =>
      h3TerminalPhysicalTopDissipation3Path
        hClass t
  | .fourthTemporal =>
      (
        ‖deriv
            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass j)
            t‖ : ℝ
      ) ^ 2
  | .sixthDiffusion =>
      (
        ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
            hH3 hClass j t‖ : ℝ
      ) ^ 2

/--
One resolved channel is cofinally unbounded at the terminal time if it exceeds
every finite threshold arbitrarily far into every strict terminal tail.
-/
def H3TerminalResolvedPhysicalPDEChannelCofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel) :
    Prop :=
  ∀ c : ℝ,
    c ∈ Set.Ioo a T →
    ∀ M : ℝ,
      ∃ t : ℝ,
        t ∈ Set.Ioo c T
          ∧
        M
          <
        h3TerminalResolvedPhysicalPDEChannelAmplitude
          hH3 hClass j channel t

/-! ## Canonical channel form of the obstruction -/

/--
Hypothetical nonextension freezes both the coordinate and the resolved
physical PDE channel.  That one scalar channel is cofinally unbounded on every
strict terminal tail.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    ∃ j₀ : Fin 3,
      ∃ channel : H3TerminalResolvedPhysicalPDEChannel,
        H3TerminalResolvedPhysicalPDEChannelCofinallyUnbounded
          hH3 hClass j₀ channel := by

  obtain
    ⟨j₀, hBranch⟩ :=
    exists_fixed_thirdRadialForcing_temporalDissipativePDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  rcases hBranch with hLower | hTop | hFourth | hSixth

  · refine
      ⟨
        j₀,
        H3TerminalResolvedPhysicalPDEChannel.lowerTemporal,
        ?_
      ⟩

    simpa [
      H3TerminalResolvedPhysicalPDEChannelCofinallyUnbounded,
      h3TerminalResolvedPhysicalPDEChannelAmplitude
    ] using hLower

  · refine
      ⟨
        j₀,
        H3TerminalResolvedPhysicalPDEChannel.topDissipation,
        ?_
      ⟩

    simpa [
      H3TerminalResolvedPhysicalPDEChannelCofinallyUnbounded,
      h3TerminalResolvedPhysicalPDEChannelAmplitude
    ] using hTop

  · refine
      ⟨
        j₀,
        H3TerminalResolvedPhysicalPDEChannel.fourthTemporal,
        ?_
      ⟩

    simpa [
      H3TerminalResolvedPhysicalPDEChannelCofinallyUnbounded,
      h3TerminalResolvedPhysicalPDEChannelAmplitude
    ] using hFourth

  · refine
      ⟨
        j₀,
        H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion,
        ?_
      ⟩

    simpa [
      H3TerminalResolvedPhysicalPDEChannelCofinallyUnbounded,
      h3TerminalResolvedPhysicalPDEChannelAmplitude
    ] using hSixth

/--
Neutral continuation formulation in canonical channel language.

Either the H³ path extends smoothly through `T`, or one fixed coordinate and
one fixed resolved physical PDE channel is cofinally unbounded on every strict
terminal tail.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_cofinallyUnbounded
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
    (
      ∃ j₀ : Fin 3,
        ∃ channel : H3TerminalResolvedPhysicalPDEChannel,
          H3TerminalResolvedPhysicalPDEChannelCofinallyUnbounded
            hH3 hClass j₀ channel
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_resolvedPhysicalPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
