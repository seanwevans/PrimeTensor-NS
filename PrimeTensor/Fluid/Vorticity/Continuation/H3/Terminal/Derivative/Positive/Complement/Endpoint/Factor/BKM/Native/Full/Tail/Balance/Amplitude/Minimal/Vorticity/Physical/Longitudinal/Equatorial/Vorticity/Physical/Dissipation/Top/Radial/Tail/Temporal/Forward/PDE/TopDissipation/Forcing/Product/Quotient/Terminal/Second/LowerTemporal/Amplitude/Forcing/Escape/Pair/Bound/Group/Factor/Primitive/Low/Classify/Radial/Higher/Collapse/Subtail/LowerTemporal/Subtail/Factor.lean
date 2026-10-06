import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Collapse

/-!
# Resolve lower and sixth derivative factors in the fixed-channel frontier

The canonical fixed-channel norm-factor alternative under hypothetical
nonextension has two branches:

* the scalar channel amplitude diverges on a cofinal extraction; or
* the natural Hilbert derivative norm of that same fixed channel diverges on
  the original terminal sequence.

Two derivative-norm channel types are now completely resolved:

* `lowerTemporal`, by the lower-temporal closure developed through the
  fourth-q forcing chain;
* `sixthDiffusion`, by the previously closed sixth-diffusion hierarchy.

Hence a genuinely unresolved derivative-norm branch can only belong to
`topDissipation` or `fourthTemporal`.  The scalar-amplitude branch is left
untouched here.

This only refines the existing exhaustive alternative; it makes no claim that
any escape branch occurs for an actual solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/--
Under hypothetical nonextension, the fixed-channel norm-factor frontier can be
refined so that derivative-norm escape remains exposed only for the
top-dissipation or fourth-temporal channels.

If the derivative branch lands in lower-temporal or sixth-diffusion instead,
it is absorbed into physical H³-energy escape or one fixed nonzero extended
higher-radial escape on a cofinal terminal subsequence.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_topFourthDerivative_or_energy_or_fixedExtendedHigherRadial_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          ∃ hτ :
            ∀ n : ℕ,
              τ n ∈ Set.Ioo a T
                ∧
              τ n ∈
                Set.Ioo
                  (T - (1 : ℝ) / ((n : ℝ) + 1))
                  T,
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
              (
                (
                  channel =
                      H3TerminalResolvedPhysicalPDEChannel.topDissipation
                    ∨
                  channel =
                      H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
                )
                  ∧
                Tendsto
                  (
                    fun n : ℕ =>
                      h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
                        hH3 hClass j₀ channel (τ n)
                  )
                  atTop
                  atTop
              )
                ∨
              (
                ∃ s : ℕ → ℕ,
                  (∀ n : ℕ, n ≤ s n)
                    ∧
                  Tendsto s atTop atTop
                    ∧
                  Tendsto
                    (fun n : ℕ => τ (s n))
                    atTop
                    (𝓝 T)
                    ∧
                  Tendsto
                    (
                      fun n : ℕ =>
                        velocityH3EnergyAt u (τ (s n))
                    )
                    atTop
                    atTop
              )
                ∨
              (
                ∃ m : ℕ,
                  m ≠ 0
                    ∧
                  ∃ s : ℕ → ℕ,
                    (∀ n : ℕ, n ≤ s n)
                      ∧
                    Tendsto s atTop atTop
                      ∧
                    Tendsto
                      (fun n : ℕ => τ (s n))
                      atTop
                      (𝓝 T)
                      ∧
                    Tendsto
                      (
                        fun n : ℕ =>
                          h3TerminalPhysicalExtendedHigherRadialMomentAt
                            hH3 hClass m
                            (τ (s n))
                            ((hτ (s n)).1)
                      )
                      atTop
                      (𝓝 ∞)
              )
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
    exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_hilbertDerivativeNorm_escapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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

  rcases hBranch with
    hAmplitude
    |
    hDerivative

  · exact
      Or.inl hAmplitude

  · cases channel with

    | lowerTemporal =>
        rcases
          lowerTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial
            hH3
            hClass
            j₀
            τ
            (fun n : ℕ => (hτ n).1)
            hTauTendsto
            hDerivative
        with
          hEnergy
          |
          hHigher

        · exact
            Or.inr
              (
                Or.inr
                  (
                    Or.inl hEnergy
                  )
              )

        · exact
            Or.inr
              (
                Or.inr
                  (
                    Or.inr hHigher
                  )
              )

    | topDissipation =>
        exact
          Or.inr
            (
              Or.inl
                ⟨
                  Or.inl rfl,
                  hDerivative
                ⟩
            )

    | fourthTemporal =>
        exact
          Or.inr
            (
              Or.inl
                ⟨
                  Or.inr rfl,
                  hDerivative
                ⟩
            )

    | sixthDiffusion =>
        rcases
          sixthDiffusion_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial
            hH3
            hClass
            j₀
            τ
            (fun n : ℕ => (hτ n).1)
            hTauTendsto
            hDerivative
        with
          hEnergy
          |
          hHigher

        · exact
            Or.inr
              (
                Or.inr
                  (
                    Or.inl hEnergy
                  )
              )

        · exact
            Or.inr
              (
                Or.inr
                  (
                    Or.inr hHigher
                  )
              )

end

end Euclidean
end Bridge
end PrimeTensor
