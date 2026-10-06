import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal

/-!
# Lower-temporal obstruction on every cofinal subtail

The preceding checkpoint reduced lower-temporal Hilbert-derivative escape to

* physical H³-energy escape, or
* escape of one fixed nonzero extended higher-radial moment.

This file records the hereditary form needed for synchronization with the
remaining terminal cascade.

If the lower-temporal derivative norm tends to `+∞` on a strict terminal
sequence, the same hypothesis persists after every cofinal reindexing.
Applying the resolved dichotomy to that reindexed sequence yields a further
cofinal refinement carrying either H³-energy escape or one fixed nonzero
higher-radial escape.
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
Every cofinal subtail of a lower-temporal Hilbert-derivative escape sequence
has a further cofinal refinement on which either physical H³ energy diverges
or one fixed nonzero extended higher-radial moment diverges.

The refinement map `s` is relative to the supplied subtail `k`; the resulting
physical times are `τ (k (s n))`.
-/
theorem lowerTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_on_every_cofinal_subtail
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
    ∀ k : ℕ → ℕ,
      Tendsto k atTop atTop
        →
      (
        (
          ∃ s : ℕ → ℕ,
            (∀ n : ℕ, n ≤ s n)
              ∧
            Tendsto s atTop atTop
              ∧
            Tendsto
              (fun n : ℕ => τ (k (s n)))
              atTop
              (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  velocityH3EnergyAt
                    u
                    (τ (k (s n)))
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
                (fun n : ℕ => τ (k (s n)))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    h3TerminalPhysicalExtendedHigherRadialMomentAt
                      hH3 hClass m
                      (τ (k (s n)))
                      (hτ (k (s n)))
                )
                atTop
                (𝓝 ∞)
        )
      ) := by

  intro k hkTop

  have hTauSub :
      Tendsto
        (fun n : ℕ => τ (k n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp hkTop

  have hLowerSub :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
              (τ (k n))
        )
        atTop
        atTop :=
    hLower.comp hkTop

  exact
    lowerTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial
      hH3
      hClass
      j
      (fun n : ℕ => τ (k n))
      (fun n : ℕ => hτ (k n))
      hTauSub
      hLowerSub

/--
Equivalent original-index packaging: on every cofinal subtail there is a
further refinement whose composite original index remains cofinal.
-/
theorem lowerTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_on_every_cofinal_subtail_composite
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
    ∀ k : ℕ → ℕ,
      Tendsto k atTop atTop
        →
      (
        (
          ∃ s : ℕ → ℕ,
            (∀ n : ℕ, n ≤ s n)
              ∧
            Tendsto
              (fun n : ℕ => k (s n))
              atTop
              atTop
              ∧
            Tendsto
              (fun n : ℕ => τ (k (s n)))
              atTop
              (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  velocityH3EnergyAt
                    u
                    (τ (k (s n)))
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
              Tendsto
                (fun n : ℕ => k (s n))
                atTop
                atTop
                ∧
              Tendsto
                (fun n : ℕ => τ (k (s n)))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    h3TerminalPhysicalExtendedHigherRadialMomentAt
                      hH3 hClass m
                      (τ (k (s n)))
                      (hτ (k (s n)))
                )
                atTop
                (𝓝 ∞)
        )
      ) := by

  intro k hkTop

  rcases
    lowerTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_on_every_cofinal_subtail
      hH3 hClass j τ hτ hTauTendsto hLower k hkTop
  with
    hEnergy
    |
    hHigher

  · rcases hEnergy with
      ⟨s, hs, hsTop, hTauSub, hEnergyTop⟩

    exact
      Or.inl
        ⟨
          s,
          hs,
          hkTop.comp hsTop,
          hTauSub,
          hEnergyTop
        ⟩

  · rcases hHigher with
      ⟨m, hm, s, hs, hsTop, hTauSub, hHigherTop⟩

    exact
      Or.inr
        ⟨
          m,
          hm,
          s,
          hs,
          hkTop.comp hsTop,
          hTauSub,
          hHigherTop
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
