import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher

/-!
# Collapse the sixth-diffusion forcing provenance into one higher-radial channel

The preceding checkpoints resolved every forcing-side primitive into either:

* ordinary physical H³-energy escape; or
* escape of an already-existing extended higher-radial moment.

The particular higher-radial shifts `4`, `10`, and `12` only record which
algebraic route produced the obstruction.  They are not distinct terminal
objects.

This file erases that provenance.  The sixth-diffusion frontier is packaged
as the neutral dichotomy

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
The two forcing-derived higher-radial shifts are strictly positive.
-/
theorem h3TerminalForcingThirdQHigherRadialShift_ne_zero
    (q : Fin 2) :
    h3TerminalForcingThirdQHigherRadialShift q ≠ 0 := by

  fin_cases q <;>
    simp [h3TerminalForcingThirdQHigherRadialShift]

/--
After all primitive forcing reductions, sixth-diffusion escape has only two
structural forms:

* physical H³ energy tends to `+∞` on a cofinal terminal subsequence; or
* one fixed nonzero member of the pre-existing extended higher-radial
  hierarchy tends to `∞` on a cofinal terminal subsequence.

The explicit shifts `4`, `10`, and `12` have been existentially packaged away.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial
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
    (hSixth :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
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
    sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_energy_or_fixedHigherRadial10_12
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    hHigherFour
    |
    hRest

  · exact
      Or.inr
        ⟨
          4,
          by norm_num,
          hHigherFour
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
            h3TerminalForcingThirdQHigherRadialShift q,
            h3TerminalForcingThirdQHigherRadialShift_ne_zero q,
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
