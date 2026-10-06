import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Subtail.StateMass.Group.Factor.Primitive.Origin.Higher.ProjectedRHSMoment10Closure

/-!
# Close the fourth-temporal derivative factor

The fixed-channel norm-factor frontier was reduced in the preceding checkpoint
so that only two derivative-norm channel types remained exposed:

* top dissipation;
* fourth temporal.

The fourth-temporal derivative branch has already been completely closed by
the projected-RHS moment-ten reduction.  Its Hilbert derivative-norm escape
forces either physical H³-energy escape or escape of one fixed nonzero
extended higher-radial moment.

Substituting that theorem leaves exactly one unresolved derivative channel:
top dissipation.

Thus hypothetical nonextension now yields one of four structural outcomes:

* scalar amplitude escape for the frozen resolved PDE channel;
* top-dissipation Hilbert derivative-norm escape;
* physical H³-energy escape;
* one fixed nonzero extended higher-radial moment escape.

No branch is asserted to occur for an actual solution.
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
After closing the fourth-temporal derivative factor, top dissipation is the
only resolved physical PDE channel whose derivative-norm escape remains
exposed.

The scalar channel-amplitude branch is deliberately retained unchanged.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_topDerivative_or_energy_or_fixedExtendedHigherRadial_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
                channel =
                    H3TerminalResolvedPhysicalPDEChannel.topDissipation
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
    exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_topFourthDerivative_or_energy_or_fixedExtendedHigherRadial_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    |
    hEnergy
    |
    hHigher

  · exact
      Or.inl hAmplitude

  · rcases hDerivative with
      ⟨hChannel, hDerivativeTop⟩

    rcases hChannel with
      hTop
      |
      hFourth

    · exact
        Or.inr
          (
            Or.inl
              ⟨
                hTop,
                hDerivativeTop
              ⟩
          )

    · subst channel

      rcases
        fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_closed
          hH3
          hClass
          j₀
          τ
          (fun n : ℕ => (hτ n).1)
          hTauTendsto
          hDerivativeTop
      with
        hEnergyFourth
        |
        hHigherFourth

      · exact
          Or.inr
            (
              Or.inr
                (
                  Or.inl hEnergyFourth
                )
            )

      · exact
          Or.inr
            (
              Or.inr
                (
                  Or.inr hHigherFourth
                )
            )

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
