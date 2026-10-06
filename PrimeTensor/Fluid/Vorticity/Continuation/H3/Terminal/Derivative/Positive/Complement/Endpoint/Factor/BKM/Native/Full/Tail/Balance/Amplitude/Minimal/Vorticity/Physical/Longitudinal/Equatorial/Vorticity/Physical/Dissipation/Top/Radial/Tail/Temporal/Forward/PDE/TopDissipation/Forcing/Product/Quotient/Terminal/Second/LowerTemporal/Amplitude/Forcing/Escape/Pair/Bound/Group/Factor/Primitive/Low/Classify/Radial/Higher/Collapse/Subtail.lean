import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse

/-!
# Fourth-temporal obstruction on every cofinal subtail

The preceding checkpoint reduced fourth-temporal amplitude escape to

* physical H³-energy escape, or
* escape of one fixed nonzero extended higher-radial moment.

This file records the hereditary form needed by the endpoint cascade.

If the fourth-temporal amplitude tends to `+∞` on a strict terminal sequence,
then the same hypothesis remains true after every cofinal reindexing. Applying
the resolved dichotomy to that reindexed sequence gives one further cofinal
refinement carrying either H³-energy escape or one fixed nonzero higher-radial
moment escape.

Thus no cofinal subtail can avoid the resolved fourth-temporal obstruction.
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
Every cofinal subtail of a fourth-temporal amplitude escape sequence has a
further cofinal refinement on which either physical H³ energy diverges or one
fixed nonzero extended higher-radial moment diverges.

The refinement map `s` is relative to the supplied subtail `k`; the resulting
physical times are `τ (k (s n))`.
-/
theorem fourthTemporal_amplitude_escape_energy_or_fixedExtendedHigherRadial_on_every_cofinal_subtail
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
    (hAmplitudeTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
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
    hTauTendsto.comp
      hkTop

  have hAmplitudeSub :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
              (τ (k n))
        )
        atTop
        atTop :=
    hAmplitudeTop.comp
      hkTop

  exact
    fourthTemporal_amplitude_escape_energy_or_fixedExtendedHigherRadial
      hH3
      hClass
      j
      (fun n : ℕ => τ (k n))
      (fun n : ℕ => hτ (k n))
      hTauSub
      hAmplitudeSub

/--
Equivalent original-index packaging: on every cofinal subtail there is a
further refinement whose composite original index remains cofinal.

This form is convenient when the resolved fourth-temporal obstruction must be
synchronized with other witnesses already indexed in the original sequence.
-/
theorem fourthTemporal_amplitude_escape_energy_or_fixedExtendedHigherRadial_on_every_cofinal_subtail_composite
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
    (hAmplitudeTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
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
    fourthTemporal_amplitude_escape_energy_or_fixedExtendedHigherRadial_on_every_cofinal_subtail
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop k hkTop
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
