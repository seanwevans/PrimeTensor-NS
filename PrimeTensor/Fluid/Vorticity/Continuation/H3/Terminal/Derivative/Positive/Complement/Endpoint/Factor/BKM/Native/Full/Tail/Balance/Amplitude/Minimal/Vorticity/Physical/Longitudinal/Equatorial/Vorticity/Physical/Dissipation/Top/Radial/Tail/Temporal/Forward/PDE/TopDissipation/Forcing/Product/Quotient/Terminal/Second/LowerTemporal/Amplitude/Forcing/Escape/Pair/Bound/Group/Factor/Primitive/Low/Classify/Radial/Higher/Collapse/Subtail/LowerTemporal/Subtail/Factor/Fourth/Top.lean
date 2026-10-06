import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.Top

/-!
# Close the top-dissipation derivative factor

The preceding checkpoint left exactly one unresolved derivative-norm channel:
top dissipation.

The top-dissipation Hilbert derivative-square envelope is already known to be
the sum of the three fourth-temporal channel amplitudes.  Divergence of that
square envelope therefore yields a cofinal subsequence and one fixed spatial
coordinate whose fourth-temporal amplitude diverges.

The fourth-temporal amplitude branch has now been completely reduced through
the fourth-q forcing chain to the two existing physical alternatives:

* physical H³-energy escape;
* escape of one fixed nonzero extended higher-radial moment.

Consequently the top-dissipation derivative-norm branch is not independent.
After this substitution there is no unresolved derivative-norm channel left
in the fixed-channel factor frontier.
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
Escape of the natural top-dissipation Hilbert derivative norm forces, after
cofinal refinement, either physical H³-energy escape or escape of one fixed
nonzero extended higher-radial moment.
-/
theorem topDissipation_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.topDissipation
              (τ n)
        )
        atTop
        atTop) :
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
                  (hτ (s n))
            )
            atTop
            (𝓝 ∞)
    ) := by

  have hNormSquareTop :
      Tendsto
        (
          fun n : ℕ =>
            (
              h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
                hH3 hClass j
                H3TerminalResolvedPhysicalPDEChannel.topDissipation
                (τ n)
            ) ^ 2
        )
        atTop
        atTop := by

    refine tendsto_atTop.2 ?_

    intro M

    let R : ℝ := max M 1

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          R
            ≤
          h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.topDissipation
            (τ n) :=
      (tendsto_atTop.1 hTop) R

    filter_upwards [hLarge] with n hn

    let X : ℝ :=
      h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.topDissipation
        (τ n)

    have hMR :
        M ≤ R := by
      dsimp only [R]
      exact le_max_left M 1

    have hR1 :
        1 ≤ R := by
      dsimp only [R]
      exact le_max_right M 1

    have hX1 :
        1 ≤ X := by
      dsimp only [X]
      exact hR1.trans hn

    have hXX :
        X ≤ X ^ 2 := by
      nlinarith

    exact
      hMR.trans
        (hn.trans hXX)

  have hSquareTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.topDissipation
              (τ n)
        )
        atTop
        atTop := by

    simpa only [
      sq_h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
    ] using hNormSquareTop

  obtain
    ⟨kStar, m, hm, hmTop, hTauM, hFourthAmplitudeTop⟩ :=
    exists_fixed_fourthTemporalAmplitude_subsequence_of_topDissipationHilbertDerivativeSquare_tendstoAtTop
      hH3 hClass j τ hTauTendsto hSquareTop

  rcases
    fourthTemporal_amplitude_escape_energy_or_fixedExtendedHigherRadial
      hH3
      hClass
      kStar
      (fun n : ℕ => τ (m n))
      (fun n : ℕ => hτ (m n))
      hTauM
      hFourthAmplitudeTop
  with
    hEnergy
    |
    hHigher

  · rcases hEnergy with
      ⟨s, hs, hsTop, hTauFinal, hEnergyTop⟩

    refine
      Or.inl
        ⟨
          (fun n : ℕ => m (s n)),
          ?_,
          hmTop.comp hsTop,
          hTauFinal,
          hEnergyTop
        ⟩

    intro n

    exact
      le_trans
        (hs n)
        (hm (s n))

  · rcases hHigher with
      ⟨p, hp, s, hs, hsTop, hTauFinal, hHigherTop⟩

    refine
      Or.inr
        ⟨
          p,
          hp,
          (fun n : ℕ => m (s n)),
          ?_,
          hmTop.comp hsTop,
          hTauFinal,
          hHigherTop
        ⟩

    intro n

    exact
      le_trans
        (hs n)
        (hm (s n))

/--
With the top-dissipation derivative branch closed, hypothetical nonextension
has no remaining derivative-norm obstruction in the fixed-channel factor
frontier.

Only the scalar channel-amplitude escape branch, H³-energy escape, or one fixed
nonzero extended higher-radial escape remains.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_energy_or_fixedExtendedHigherRadial_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_topDerivative_or_energy_or_fixedExtendedHigherRadial_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    hTopDerivative
    |
    hEnergy
    |
    hHigher

  · exact
      Or.inl hAmplitude

  · rcases hTopDerivative with
      ⟨hChannel, hDerivativeTop⟩

    subst channel

    rcases
      topDissipation_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial
        hH3
        hClass
        j₀
        τ
        (fun n : ℕ => (hτ n).1)
        hTauTendsto
        hDerivativeTop
    with
      hEnergyTop
      |
      hHigherTop

    · exact
        Or.inr
          (
            Or.inl hEnergyTop
          )

    · exact
        Or.inr
          (
            Or.inr hHigherTop
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
