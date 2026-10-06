import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.Final
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude

/-!
# Remove the second-q derivative from the lower-temporal obstruction

The existing lower-temporal split gives either

* fourth-temporal state-amplitude escape on a cofinal subsequence, or
* terminal second-q forcing-derivative escape.

The latter branch is now completely resolved by
`h3TerminalSecondQForcingDerivative_escape_energy_or_fixedExtendedHigherRadial`.

Hence the only unresolved lower-temporal side is the fourth-temporal amplitude
branch.
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
A lower-temporal Hilbert derivative escape has only three remaining physical
outcomes:

1. fourth-temporal state-amplitude escape on a cofinal subsequence;
2. physical H³-energy escape on a cofinal subsequence;
3. one fixed nonzero extended higher-radial velocity moment escapes on a
   cofinal subsequence.

In particular, terminal second-q forcing-derivative escape is no longer an
independent obstruction.
-/
theorem lowerTemporal_hilbertDerivativeNorm_escape_amplitude_or_energy_or_fixedExtendedHigherRadial
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
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
            (τ n))
        atTop atTop) :
    (
      ∃ k : ℕ → ℕ,
        (∀ n : ℕ, n ≤ k n) ∧
        Tendsto k atTop atTop ∧
        Tendsto
          (fun n : ℕ => τ (k n))
          atTop
          (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
              (τ (k n)))
          atTop
          atTop
    )
      ∨
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            velocityH3EnergyAt u (τ (s n)))
          atTop
          atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto
            (fun n : ℕ => τ (s n))
            atTop
            (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop
            (𝓝 ∞)
    ) := by

  rcases
    lowerTemporal_hilbertDerivativeNorm_escape_amplitude_or_forcingDerivative
      hH3 hClass j τ hτ hTauTendsto hLower
  with hAmplitude | hSecondQ

  · exact
      Or.inl hAmplitude

  · rcases
      h3TerminalSecondQForcingDerivative_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass j τ hτ hTauTendsto hSecondQ
    with hEnergy | hHigher

    · exact
        Or.inr
          (Or.inl hEnergy)

    · exact
        Or.inr
          (Or.inr hHigher)

end

end Euclidean
end Bridge
end PrimeTensor
