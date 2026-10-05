import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor

/-!
# Norm form of the resolved-channel Hilbert derivative branch

The factor split leaves one genuinely new alternative: the square magnitude of
the Hilbert-state derivative behind one fixed resolved physical PDE channel
tends to `+∞`.

This file converts that square quantity into its natural norm scale.

For the three coordinate channels this is simply the Hilbert norm of the state
derivative.  For top dissipation it is the Euclidean `ℓ²` norm of the three
fourth-radial state derivatives,

    sqrt (∑ k, ‖V₄,k'(t)‖²).

Thus the fixed-channel factor alternative can be stated directly as

* canonical channel amplitude divergence on a cofinal extraction; or
* canonical Hilbert derivative norm divergence on the original terminal
  sequence.

No further branch or coordinate extraction is introduced here.
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
Natural norm scale of the Hilbert-state derivative behind one resolved physical
PDE channel.
-/
noncomputable def h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (t : ℝ) :
    ℝ :=
  Real.sqrt
    (
      h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
        hH3 hClass j channel t
    )

/--
The derivative-square envelope is nonnegative for every resolved channel.
-/
theorem h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel) :
    0
      ≤
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
      hH3 hClass j channel t := by

  cases channel with

  | lowerTemporal =>
      exact
        sq_nonneg
          ‖deriv
            (h3TerminalResolvedLowerTemporalHilbertState
              hH3 hClass j)
            t‖

  | topDissipation =>
      exact
        Finset.sum_nonneg
          (
            fun k hk =>
              sq_nonneg
                ‖deriv
                  (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                    hH3 hClass k)
                  t‖
          )

  | fourthTemporal =>
      exact
        sq_nonneg
          ‖deriv
            (h3TerminalResolvedFourthTemporalHilbertState
              hH3 hClass j)
            t‖

  | sixthDiffusion =>
      exact
        sq_nonneg
          ‖deriv
            (h3TerminalResolvedSixthDiffusionHilbertState
              hH3 hClass j)
            t‖

/--
The square of the canonical derivative norm envelope is exactly the
derivative-square envelope.
-/
theorem sq_h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel) :
    (
      h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
        hH3 hClass j channel t
    ) ^ 2
      =
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
      hH3 hClass j channel t := by

  unfold
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope

  exact
    Real.sq_sqrt
      (
        h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope_nonneg
          hH3 hClass j channel
      )

/--
On the lower-temporal channel the norm envelope is the ordinary Hilbert norm
of the derivative of the lower-temporal state.
-/
@[simp]
theorem h3TerminalResolvedLowerTemporalHilbertDerivativeNormEnvelope_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) :
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
        t
      =
    ‖deriv
      (h3TerminalResolvedLowerTemporalHilbertState
        hH3 hClass j)
      t‖ := by

  simp [
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope,
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg
  ]

/--
On the fourth-temporal channel the norm envelope is the ordinary Hilbert norm
of the derivative of the fourth-temporal state.
-/
@[simp]
theorem h3TerminalResolvedFourthTemporalHilbertDerivativeNormEnvelope_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) :
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
        t
      =
    ‖deriv
      (h3TerminalResolvedFourthTemporalHilbertState
        hH3 hClass j)
      t‖ := by

  simp [
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope,
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg
  ]

/--
On the sixth-diffusion channel the norm envelope is the ordinary Hilbert norm
of the derivative of the sixth-diffusion state.
-/
@[simp]
theorem h3TerminalResolvedSixthDiffusionHilbertDerivativeNormEnvelope_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) :
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
        t
      =
    ‖deriv
      (h3TerminalResolvedSixthDiffusionHilbertState
        hH3 hClass j)
      t‖ := by

  simp [
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope,
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg
  ]

/--
Under hypothetical nonextension, the fixed-channel factor alternative can be
expressed at the natural norm scale.

Either a cofinal extraction makes the canonical scalar channel amplitude tend
to `+∞`, or the canonical Hilbert derivative norm tends to `+∞` along the full
original terminal sequence.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_hilbertDerivativeNorm_escapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          )
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          (
            (
              ∃ k : ℕ → ℕ,
                (∀ n : ℕ, n ≤ k n)
                  ∧
                Tendsto k atTop atTop
                  ∧
                Tendsto
                  (fun n : ℕ => τ (k n))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (
                    fun n : ℕ =>
                      h3TerminalResolvedPhysicalPDEChannelAmplitude
                        hH3 hClass j₀ channel (τ (k n))
                  )
                  atTop
                  atTop
            )
              ∨
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
                    hH3 hClass j₀ channel (τ n)
              )
              atTop
              atTop
          ) := by

  obtain
    ⟨
      j₀,
      channel,
      τ,
      hτ,
      hTauTendsto,
      hBranch
    ⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_hilbertDerivativeSquare_escapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  refine
    ⟨
      j₀,
      channel,
      τ,
      hτ,
      hTauTendsto,
      ?_
    ⟩

  rcases hBranch with hAmplitude | hDerivativeSquare

  · exact Or.inl hAmplitude

  · exact
      Or.inr
        (
          Real.tendsto_sqrt_atTop.comp
            hDerivativeSquare
        )

/--
Neutral continuation form of the norm-scale factor alternative.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_amplitude_or_hilbertDerivativeNorm_escapeSequence
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
          ∃ τ : ℕ → ℝ,
            (
              ∀ n : ℕ,
                τ n ∈ Set.Ioo a T
                  ∧
                τ n ∈
                  Set.Ioo
                    (T - (1 : ℝ) / ((n : ℝ) + 1))
                    T
            )
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            (
              (
                ∃ k : ℕ → ℕ,
                  (∀ n : ℕ, n ≤ k n)
                    ∧
                  Tendsto k atTop atTop
                    ∧
                  Tendsto
                    (fun n : ℕ => τ (k n))
                    atTop
                    (𝓝 T)
                    ∧
                  Tendsto
                    (
                      fun n : ℕ =>
                        h3TerminalResolvedPhysicalPDEChannelAmplitude
                          hH3 hClass j₀ channel (τ (k n))
                    )
                    atTop
                    atTop
              )
                ∨
              Tendsto
                (
                  fun n : ℕ =>
                    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
                      hH3 hClass j₀ channel (τ n)
                )
                atTop
                atTop
            )
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_hilbertDerivativeNorm_escapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
