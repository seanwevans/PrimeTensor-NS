import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Sixth

/-!
# Resolve fourth-temporal and sixth-diffusion scalar amplitude channels

The derivative-norm side of the fixed-channel frontier is now completely
closed.  The remaining unresolved branch is scalar channel-amplitude escape
for one frozen resolved physical PDE channel.

Two of the four scalar channels are already completely classified:

* fourth-temporal amplitude escape resolves into physical H³-energy escape or
  one fixed nonzero extended higher-radial moment;
* sixth-diffusion amplitude escape is directly dominated by the shift-two
  extended higher-radial moment.

Substituting those closures leaves only the lower-temporal and top-dissipation
scalar amplitudes as genuinely unresolved channel amplitudes.

No new PDE estimate is introduced here.
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
Under hypothetical nonextension, after resolving the fourth-temporal and
sixth-diffusion scalar amplitudes, an unresolved scalar channel amplitude can
only be lower-temporal or top-dissipation.

The other alternatives are physical H³-energy escape or escape of one fixed
nonzero extended higher-radial moment.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_lowerTopAmplitude_or_energy_or_fixedExtendedHigherRadial_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
                (
                  channel =
                      H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
                    ∨
                  channel =
                      H3TerminalResolvedPhysicalPDEChannel.topDissipation
                )
                  ∧
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
    exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_energy_or_fixedExtendedHigherRadial_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    hEnergy
    |
    hHigher

  · rcases hAmplitude with
      ⟨k, hk, hkTop, hTauK, hAmplitudeTop⟩

    cases channel with

    | lowerTemporal =>
        exact
          Or.inl
            ⟨
              Or.inl rfl,
              k,
              hk,
              hkTop,
              hTauK,
              hAmplitudeTop
            ⟩

    | topDissipation =>
        exact
          Or.inl
            ⟨
              Or.inr rfl,
              k,
              hk,
              hkTop,
              hTauK,
              hAmplitudeTop
            ⟩

    | fourthTemporal =>
        rcases
          fourthTemporal_amplitude_escape_energy_or_fixedExtendedHigherRadial
            hH3
            hClass
            j₀
            (fun n : ℕ => τ (k n))
            (fun n : ℕ => (hτ (k n)).1)
            hTauK
            hAmplitudeTop
        with
          hEnergyFourth
          |
          hHigherFourth

        · rcases hEnergyFourth with
            ⟨s, hs, hsTop, hTauFinal, hEnergyTop⟩

          have hComp :
              ∀ n : ℕ,
                n ≤ k (s n) := by
            intro n
            exact
              le_trans
                (hs n)
                (hk (s n))

          have hCompTop :
              Tendsto
                (fun n : ℕ => k (s n))
                atTop
                atTop :=
            hkTop.comp hsTop

          exact
            Or.inr
              (
                Or.inl
                  ⟨
                    (fun n : ℕ => k (s n)),
                    hComp,
                    hCompTop,
                    hTauFinal,
                    hEnergyTop
                  ⟩
              )

        · rcases hHigherFourth with
            ⟨m, hm, s, hs, hsTop, hTauFinal, hHigherTop⟩

          have hComp :
              ∀ n : ℕ,
                n ≤ k (s n) := by
            intro n
            exact
              le_trans
                (hs n)
                (hk (s n))

          have hCompTop :
              Tendsto
                (fun n : ℕ => k (s n))
                atTop
                atTop :=
            hkTop.comp hsTop

          exact
            Or.inr
              (
                Or.inr
                  ⟨
                    m,
                    hm,
                    (fun n : ℕ => k (s n)),
                    hComp,
                    hCompTop,
                    hTauFinal,
                    hHigherTop
                  ⟩
              )

    | sixthDiffusion =>
        have hHigherTop :=
          extendedHigherRadialMoment_two_tendsto_top_of_sixthDiffusionAmplitude_tendstoAtTop
            hH3
            hClass
            j₀
            (fun n : ℕ => τ (k n))
            (fun n : ℕ => (hτ (k n)).1)
            hAmplitudeTop

        exact
          Or.inr
            (
              Or.inr
                ⟨
                  2,
                  by norm_num,
                  k,
                  hk,
                  hkTop,
                  hTauK,
                  hHigherTop
                ⟩
            )

  · exact
      Or.inr
        (
          Or.inl hEnergy
        )

  · exact
      Or.inr
        (
          Or.inr hHigher
        )

end

end Euclidean
end Bridge
end PrimeTensor
