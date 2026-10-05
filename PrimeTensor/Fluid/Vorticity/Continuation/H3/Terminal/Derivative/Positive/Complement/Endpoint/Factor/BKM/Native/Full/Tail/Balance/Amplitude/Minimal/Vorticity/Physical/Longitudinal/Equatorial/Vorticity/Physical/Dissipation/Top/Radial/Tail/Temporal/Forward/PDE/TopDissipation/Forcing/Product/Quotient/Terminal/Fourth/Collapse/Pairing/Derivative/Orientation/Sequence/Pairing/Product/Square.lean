import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product

/-!
# Square-energy envelope for the resolved-channel Hilbert product

The canonical Hilbert product envelope is already forced to diverge along one
fixed resolved-channel terminal sequence under hypothetical nonextension.

The elementary inequality

    2 a b ≤ a² + b²

for nonnegative Hilbert norms gives a more symmetric carrier of that growth:
the sum of the Hilbert-state square and Hilbert-state-derivative square.

For the three coordinate channels this is

    ‖X(t)‖² + ‖X'(t)‖².

For top dissipation it is the finite coordinate sum of the corresponding
fourth-radial terms.

Thus the same terminal sequence carries divergence of a nonnegative quadratic
state/derivative energy.  This still deliberately does not choose whether the
state norm or its derivative norm is the escaping factor.
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
Quadratic state/derivative envelope for one resolved physical PDE channel.
-/
noncomputable def h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope
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
      ‖h3TerminalResolvedLowerTemporalHilbertState
        hH3 hClass j t‖ ^ 2
        +
      ‖deriv
        (h3TerminalResolvedLowerTemporalHilbertState
          hH3 hClass j)
        t‖ ^ 2
  | .topDissipation =>
      ∑ k : Fin 3,
        (
          ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass k t‖ ^ 2
            +
          ‖deriv
            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass k)
            t‖ ^ 2
        )
  | .fourthTemporal =>
      ‖h3TerminalResolvedFourthTemporalHilbertState
        hH3 hClass j t‖ ^ 2
        +
      ‖deriv
        (h3TerminalResolvedFourthTemporalHilbertState
          hH3 hClass j)
        t‖ ^ 2
  | .sixthDiffusion =>
      ‖h3TerminalResolvedSixthDiffusionHilbertState
        hH3 hClass j t‖ ^ 2
        +
      ‖deriv
        (h3TerminalResolvedSixthDiffusionHilbertState
          hH3 hClass j)
        t‖ ^ 2

private theorem two_mul_le_sq_add_sq
    (a b : ℝ) :
    2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/--
The Hilbert product envelope is bounded by the quadratic state/derivative
envelope.
-/
theorem h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope_le_factorSquareEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel) :
    h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope
        hH3 hClass j channel t
      ≤
    h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope
      hH3 hClass j channel t := by

  cases channel with

  | lowerTemporal =>
      exact
        two_mul_le_sq_add_sq
          ‖h3TerminalResolvedLowerTemporalHilbertState
            hH3 hClass j t‖
          ‖deriv
            (h3TerminalResolvedLowerTemporalHilbertState
              hH3 hClass j)
            t‖

  | topDissipation =>

      apply Finset.sum_le_sum

      intro k hk

      exact
        two_mul_le_sq_add_sq
          ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass k t‖
          ‖deriv
            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass k)
            t‖

  | fourthTemporal =>
      exact
        two_mul_le_sq_add_sq
          ‖h3TerminalResolvedFourthTemporalHilbertState
            hH3 hClass j t‖
          ‖deriv
            (h3TerminalResolvedFourthTemporalHilbertState
              hH3 hClass j)
            t‖

  | sixthDiffusion =>
      exact
        two_mul_le_sq_add_sq
          ‖h3TerminalResolvedSixthDiffusionHilbertState
            hH3 hClass j t‖
          ‖deriv
            (h3TerminalResolvedSixthDiffusionHilbertState
              hH3 hClass j)
            t‖

/--
Under hypothetical nonextension, the same fixed resolved-channel terminal
sequence carries quadratic state/derivative energy above every index, and that
quadratic envelope tends to `+∞`.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_hilbertFactorSquareEnvelopeEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
              h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope
                hH3 hClass j₀ channel (τ n)
          )
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope
                  hH3 hClass j₀ channel (τ n)
            )
            atTop
            atTop := by

  obtain
    ⟨
      j₀,
      channel,
      τ,
      hτ,
      hTauTendsto,
      hProductTendsto
    ⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_hilbertProductEnvelopeEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  have hSquareData :
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
        h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope
          hH3 hClass j₀ channel (τ n) := by

    intro n

    have hProductLeSquare :=
      h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope_le_factorSquareEnvelope
        (t := τ n)
        hH3 hClass j₀ channel

    exact
      ⟨
        (hτ n).1,
        (hτ n).2.1,
        lt_of_lt_of_le
          (hτ n).2.2
          hProductLeSquare
      ⟩

  have hSquareTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope
              hH3 hClass j₀ channel (τ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hProductEventually :
        ∀ᶠ n : ℕ in atTop,
          M
            ≤
          h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope
            hH3 hClass j₀ channel (τ n) :=
      (tendsto_atTop.1 hProductTendsto) M

    filter_upwards
      [hProductEventually]
      with n hn

    exact
      le_trans
        hn
        (
          h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope_le_factorSquareEnvelope
            (t := τ n)
            hH3 hClass j₀ channel
        )

  exact
    ⟨
      j₀,
      channel,
      τ,
      hSquareData,
      hTauTendsto,
      hSquareTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
