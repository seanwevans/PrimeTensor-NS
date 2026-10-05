import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence

/-!
# Terminal escape sequence for the canonical resolved-channel Hilbert pairing

The preceding checkpoint extracted a strict terminal sequence along which one
fixed oriented resolved-channel scalar amplitude derivative tends to `+∞`.

But the scalar derivative has already been identified pointwise, at every
strict preterminal time, with the canonical Hilbert pairing of that same
resolved channel.  Therefore the identical sequence carries the stronger
physical statement

    n < orientedValue s (pairing(channel, τ n))

and the oriented pairing itself tends to `+∞`.

This is only an exact transport through the derivative/pairing identity.  In
particular, no physical-clock rate such as
`(T - τ n) * |pairing(channel, τ n)| -> +∞` is asserted.
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
Under hypothetical nonextension, one fixed coordinate, one fixed resolved
physical PDE channel, and one fixed orientation admit a quantitatively
localized terminal sequence along which the canonical oriented Hilbert pairing
tends to `+∞`.
-/
theorem exists_fixed_oriented_resolvedPhysicalPDEChannel_hilbertPairingEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
        ∃ s : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            (
              ∀ n : ℕ,
                τ n ∈ Set.Ioo a T
                  ∧
                τ n ∈
                  Set.Ioo
                    (T - (1 : ℝ) / ((n : ℝ) + 1))
                    T
                  ∧
                (n : ℝ)
                  <
                h3TerminalOrientedValue
                  s
                  (
                    h3TerminalResolvedPhysicalPDEChannelHilbertPairing
                      hH3 hClass j₀ channel (τ n)
                  )
            )
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalOrientedValue
                    s
                    (
                      h3TerminalResolvedPhysicalPDEChannelHilbertPairing
                        hH3 hClass j₀ channel (τ n)
                    )
              )
              atTop
              atTop := by

  obtain
    ⟨
      j₀,
      channel,
      s,
      τ,
      hτ,
      hTauTendsto,
      hDerivativeTendsto
    ⟩ :=
    exists_fixed_oriented_resolvedPhysicalPDEChannel_amplitudeDerivativeEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  have hPairData :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T
          ∧
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T
          ∧
        (n : ℝ)
          <
        h3TerminalOrientedValue
          s
          (
            h3TerminalResolvedPhysicalPDEChannelHilbertPairing
              hH3 hClass j₀ channel (τ n)
          ) := by

    intro n

    have hDerivativeEq :=
      deriv_h3TerminalResolvedPhysicalPDEChannelAmplitude_eq_hilbertPairing
        hH3 hClass j₀ channel (hτ n).1

    refine
      ⟨
        (hτ n).1,
        (hτ n).2.1,
        ?_
      ⟩

    rw [← hDerivativeEq]

    exact
      (hτ n).2.2

  have hSequenceEq :
      (
        fun n : ℕ =>
          h3TerminalOrientedValue
            s
            (
              deriv
                (
                  h3TerminalResolvedPhysicalPDEChannelAmplitude
                    hH3 hClass j₀ channel
                )
                (τ n)
            )
      )
        =
      (
        fun n : ℕ =>
          h3TerminalOrientedValue
            s
            (
              h3TerminalResolvedPhysicalPDEChannelHilbertPairing
                hH3 hClass j₀ channel (τ n)
            )
      ) := by

    funext n

    rw [
      deriv_h3TerminalResolvedPhysicalPDEChannelAmplitude_eq_hilbertPairing
        hH3 hClass j₀ channel (hτ n).1
    ]

  rw [hSequenceEq] at hDerivativeTendsto

  exact
    ⟨
      j₀,
      channel,
      s,
      τ,
      hPairData,
      hTauTendsto,
      hDerivativeTendsto
    ⟩

/--
Neutral sequential formulation with the surviving terminal escape written
directly as one fixed oriented canonical Hilbert pairing.
-/
theorem smoothContinuationExtension_or_fixed_oriented_resolvedPhysicalPDEChannel_hilbertPairingEscapeSequence
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
          ∃ s : H3TerminalOrientation,
            ∃ τ : ℕ → ℝ,
              (
                ∀ n : ℕ,
                  τ n ∈ Set.Ioo a T
                    ∧
                  τ n ∈
                    Set.Ioo
                      (T - (1 : ℝ) / ((n : ℝ) + 1))
                      T
                    ∧
                  (n : ℝ)
                    <
                  h3TerminalOrientedValue
                    s
                    (
                      h3TerminalResolvedPhysicalPDEChannelHilbertPairing
                        hH3 hClass j₀ channel (τ n)
                    )
              )
                ∧
              Tendsto τ atTop (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    h3TerminalOrientedValue
                      s
                      (
                        h3TerminalResolvedPhysicalPDEChannelHilbertPairing
                          hH3 hClass j₀ channel (τ n)
                      )
                )
                atTop
                atTop
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
          exists_fixed_oriented_resolvedPhysicalPDEChannel_hilbertPairingEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
