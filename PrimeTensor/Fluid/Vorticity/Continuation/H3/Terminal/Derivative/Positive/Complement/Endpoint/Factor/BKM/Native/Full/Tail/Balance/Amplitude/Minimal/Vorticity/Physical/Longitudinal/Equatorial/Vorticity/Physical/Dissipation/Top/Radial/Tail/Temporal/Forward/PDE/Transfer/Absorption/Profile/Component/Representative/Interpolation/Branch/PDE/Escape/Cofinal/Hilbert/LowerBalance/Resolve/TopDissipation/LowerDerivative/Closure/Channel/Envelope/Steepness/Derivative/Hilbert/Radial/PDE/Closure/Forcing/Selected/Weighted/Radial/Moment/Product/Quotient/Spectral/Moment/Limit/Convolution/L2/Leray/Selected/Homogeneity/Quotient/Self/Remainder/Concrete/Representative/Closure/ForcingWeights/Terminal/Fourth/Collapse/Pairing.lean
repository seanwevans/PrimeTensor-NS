import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse

/-!
# Canonical resolved-channel Hilbert pairing

The four remaining fixed-channel alternatives are now all explicit Hilbert
pairings.  This file packages them on the existing
`H3TerminalResolvedPhysicalPDEChannel` enum, exactly as `Channel.lean`
previously packaged the four scalar amplitudes.

For the three coordinate channels the pairing is

    2 ⟪X_j(t), X_j'(t)⟫_ℝ.

For top dissipation it is the finite coordinate sum

    ∑ k, 2 ⟪V₄,k(t), V₄,k'(t)⟫_ℝ,

which is the derivative pairing of the full top-dissipation amplitude.

No new analytic estimate is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

/--
Canonical real Hilbert pairing attached to one resolved physical PDE channel.

The coordinate argument is retained uniformly even though the top-dissipation
pairing is the full finite coordinate sum.
-/
noncomputable def h3TerminalResolvedPhysicalPDEChannelHilbertPairing
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
      2 *
        inner ℝ
          (h3TerminalResolvedLowerTemporalHilbertState
            hH3 hClass j t)
          (
            deriv
              (h3TerminalResolvedLowerTemporalHilbertState
                hH3 hClass j)
              t
          )
  | .topDissipation =>
      ∑ k : Fin 3,
        2 *
          inner ℝ
            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass k t)
            (
              deriv
                (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass k)
                t
            )
  | .fourthTemporal =>
      2 *
        inner ℝ
          (h3TerminalResolvedFourthTemporalHilbertState
            hH3 hClass j t)
          (
            deriv
              (h3TerminalResolvedFourthTemporalHilbertState
                hH3 hClass j)
              t
          )
  | .sixthDiffusion =>
      2 *
        inner ℝ
          (h3TerminalResolvedSixthDiffusionHilbertState
            hH3 hClass j t)
          (
            deriv
              (h3TerminalResolvedSixthDiffusionHilbertState
                hH3 hClass j)
              t
          )

/--
One resolved channel has cofinally unbounded Hilbert pairing magnitude if its
absolute pairing exceeds every finite threshold arbitrarily far into every
strict terminal tail.
-/
def H3TerminalResolvedPhysicalPDEChannelHilbertPairingCofinallyUnbounded
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
      ∃ r : ℝ,
        r ∈ Set.Ioo c T
          ∧
        M
          <
        abs
          (
            h3TerminalResolvedPhysicalPDEChannelHilbertPairing
              hH3 hClass j channel r
          )

/--
Under hypothetical nonextension, one fixed coordinate and one fixed resolved
physical PDE channel have cofinally unbounded Hilbert pairing magnitude.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_hilbertPairingCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
        H3TerminalResolvedPhysicalPDEChannelHilbertPairingCofinallyUnbounded
          hH3 hClass j₀ channel := by

  obtain
    ⟨j₀, hBranch⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_pairingCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  rcases hBranch with hLower | hTop | hFourth | hSixth

  · refine
      ⟨
        j₀,
        H3TerminalResolvedPhysicalPDEChannel.lowerTemporal,
        ?_
      ⟩

    simpa [
      H3TerminalResolvedPhysicalPDEChannelHilbertPairingCofinallyUnbounded,
      h3TerminalResolvedPhysicalPDEChannelHilbertPairing
    ] using hLower

  · refine
      ⟨
        j₀,
        H3TerminalResolvedPhysicalPDEChannel.topDissipation,
        ?_
      ⟩

    simpa [
      H3TerminalResolvedPhysicalPDEChannelHilbertPairingCofinallyUnbounded,
      h3TerminalResolvedPhysicalPDEChannelHilbertPairing
    ] using hTop

  · refine
      ⟨
        j₀,
        H3TerminalResolvedPhysicalPDEChannel.fourthTemporal,
        ?_
      ⟩

    simpa [
      H3TerminalResolvedPhysicalPDEChannelHilbertPairingCofinallyUnbounded,
      h3TerminalResolvedPhysicalPDEChannelHilbertPairing
    ] using hFourth

  · refine
      ⟨
        j₀,
        H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion,
        ?_
      ⟩

    simpa [
      H3TerminalResolvedPhysicalPDEChannelHilbertPairingCofinallyUnbounded,
      h3TerminalResolvedPhysicalPDEChannelHilbertPairing
    ] using hSixth

/--
Neutral continuation form with the nonextension side reduced to one fixed
resolved-channel Hilbert pairing escape.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_hilbertPairingCofinallyUnbounded
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
          H3TerminalResolvedPhysicalPDEChannelHilbertPairingCofinallyUnbounded
            hH3 hClass j₀ channel
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_resolvedPhysicalPDEChannel_hilbertPairingCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
