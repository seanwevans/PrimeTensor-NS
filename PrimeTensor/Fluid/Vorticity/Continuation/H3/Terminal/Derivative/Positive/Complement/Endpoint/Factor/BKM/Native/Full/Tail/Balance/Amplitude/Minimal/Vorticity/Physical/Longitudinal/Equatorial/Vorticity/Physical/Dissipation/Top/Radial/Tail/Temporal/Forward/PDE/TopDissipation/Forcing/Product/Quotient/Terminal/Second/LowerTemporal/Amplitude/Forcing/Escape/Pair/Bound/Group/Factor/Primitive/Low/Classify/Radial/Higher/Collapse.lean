import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher

/-!
# Collapse the fourth-temporal forcing provenance into one higher-radial channel

The preceding checkpoints resolved every fourth-q forcing-side primitive into
either:

* ordinary physical H³-energy escape; or
* escape of an already-existing extended higher-radial moment.

The particular higher-radial shifts `2`, `6`, and `8` only record which
algebraic route produced the obstruction.  They are not distinct terminal
objects.

This file erases that provenance and packages the fourth-temporal frontier as
the neutral dichotomy

    H³-energy escape
      or
    one fixed nonzero extended higher-radial moment escapes.

No assertion is made that either branch occurs for an actual solution.
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
The two forcing-derived fourth-q higher-radial shifts are strictly positive.
-/
theorem h3TerminalForcingFourthQHigherRadialShift_ne_zero
    (q : Fin 2) :
    h3TerminalForcingFourthQHigherRadialShift q ≠ 0 := by

  fin_cases q <;>
    simp [h3TerminalForcingFourthQHigherRadialShift]

/--
After all primitive fourth-q forcing reductions, fourth-temporal amplitude
escape has only two structural forms:

* physical H³ energy tends to `+∞` on a cofinal terminal subsequence; or
* one fixed nonzero member of the pre-existing extended higher-radial
  hierarchy tends to `∞` on a cofinal terminal subsequence.

The explicit shifts `2`, `6`, and `8` have been existentially packaged away.
-/
theorem fourthTemporal_amplitude_escape_energy_or_fixedExtendedHigherRadial
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
    fourthTemporal_amplitude_escape_extendedHigherTwo_or_energy_or_fixedHigherRadial6_8
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop
  with
    hHigherTwo
    |
    hRest

  · exact
      Or.inr
        ⟨
          2,
          by norm_num,
          hHigherTwo
        ⟩

  · rcases hRest with
      hEnergy
      |
      hHigher

    · exact
        Or.inl
          hEnergy

    · rcases hHigher with
        ⟨q, s, hs, hsTop, hTauSub, hHigherTop⟩

      exact
        Or.inr
          ⟨
            h3TerminalForcingFourthQHigherRadialShift q,
            h3TerminalForcingFourthQHigherRadialShift_ne_zero q,
            s,
            hs,
            hsTop,
            hTauSub,
            hHigherTop
          ⟩

end

end Euclidean
end Bridge
end PrimeTensor
