import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal

/-!
# Collapse the lower-temporal obstruction

The earlier lower-temporal reduction left three physical outcomes:

* fourth-temporal state-amplitude escape on a cofinal subsequence;
* physical H³-energy escape;
* escape of one fixed nonzero extended higher-radial moment.

The fourth-temporal amplitude branch has now itself been completely resolved
into physical H³-energy escape or fixed nonzero higher-radial escape.

Substituting that resolution removes the last intermediate PDE-channel
amplitude from the lower-temporal frontier.  Lower-temporal Hilbert-derivative
escape therefore has only two structural outcomes:

* physical H³-energy escape;
* escape of one fixed nonzero extended higher-radial moment.

No claim is made that either alternative actually occurs.
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
Lower-temporal Hilbert-derivative escape resolves completely into either
physical H³-energy escape or one fixed nonzero member of the pre-existing
extended higher-radial hierarchy on a cofinal terminal subsequence.
-/
theorem lowerTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial
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
    (hLower :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
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

  rcases
    lowerTemporal_hilbertDerivativeNorm_escape_amplitude_or_energy_or_fixedExtendedHigherRadial
      hH3 hClass j τ hτ hTauTendsto hLower
  with
    hAmplitude
    |
    hRest

  · rcases hAmplitude with
      ⟨k, hk, hkTop, hTauK, hAmplitudeTop⟩

    rcases
      fourthTemporal_amplitude_escape_energy_or_fixedExtendedHigherRadial
        hH3
        hClass
        j
        (fun n : ℕ => τ (k n))
        (fun n : ℕ => hτ (k n))
        hTauK
        hAmplitudeTop
    with
      hEnergy
      |
      hHigher

    · rcases hEnergy with
        ⟨s, hs, hsTop, hTauSub, hEnergyTop⟩

      refine
        Or.inl
          ⟨
            (fun n : ℕ => k (s n)),
            ?_,
            hkTop.comp hsTop,
            hTauSub,
            hEnergyTop
          ⟩

      intro n

      exact
        le_trans
          (hs n)
          (hk (s n))

    · rcases hHigher with
        ⟨m, hm, s, hs, hsTop, hTauSub, hHigherTop⟩

      refine
        Or.inr
          ⟨
            m,
            hm,
            (fun n : ℕ => k (s n)),
            ?_,
            hkTop.comp hsTop,
            hTauSub,
            hHigherTop
          ⟩

      intro n

      exact
        le_trans
          (hs n)
          (hk (s n))

  · rcases hRest with
      hEnergy
      |
      hHigher

    · exact
        Or.inl hEnergy

    · exact
        Or.inr hHigher

end

end Euclidean
end Bridge
end PrimeTensor
