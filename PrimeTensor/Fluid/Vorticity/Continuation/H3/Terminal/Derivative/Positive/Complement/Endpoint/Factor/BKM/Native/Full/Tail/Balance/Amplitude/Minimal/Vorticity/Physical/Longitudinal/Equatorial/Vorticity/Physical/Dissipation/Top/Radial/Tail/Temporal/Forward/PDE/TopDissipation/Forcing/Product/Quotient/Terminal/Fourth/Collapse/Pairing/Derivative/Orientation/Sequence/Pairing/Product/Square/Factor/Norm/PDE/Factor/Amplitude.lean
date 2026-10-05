import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor

/-!
# Normalize the lower resolved derivative factor to canonical amplitude

The lower-temporal derivative factor split produced the alternative

    ‖X₂,j‖ -> +∞ on a cofinal subsequence

or

    ‖(q F_j)'‖ -> +∞

on the original terminal sequence.

But `‖X₂,j‖²` is exactly the canonical fourth-temporal channel amplitude.
Therefore the first branch can be rewritten entirely in the already-canonical
resolved-channel language.

The fourth-temporal factor split is already on its natural frontier:

    sixth-diffusion derivative norm

versus

    ‖(q² F_j)'‖.

This file packages those two statements side by side.
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
If the norm of an `H3FourierComplexL2` sequence tends to `+∞`, then its squared
norm also tends to `+∞`.
-/
private theorem tendsto_norm_sq_atTop_of_norm_tendstoAtTop
    (X : ℕ → H3FourierComplexL2)
    (hX :
      Tendsto
        (fun n : ℕ => ‖X n‖)
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ => ‖X n‖ ^ 2)
      atTop
      atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro M

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        max 1 M
          ≤
        ‖X n‖ :=
    (tendsto_atTop.1 hX)
      (max 1 M)

  filter_upwards
    [hLarge]
    with n hn

  have hOne :
      (1 : ℝ) ≤ ‖X n‖ :=
    le_trans
      (le_max_left 1 M)
      hn

  have hM :
      M ≤ ‖X n‖ :=
    le_trans
      (le_max_right 1 M)
      hn

  nlinarith [
    sq_nonneg (‖X n‖ - 1)
  ]

/--
Lower-temporal Hilbert derivative escape resolves into either canonical
fourth-temporal amplitude escape on a cofinal subsequence, or terminal
`q F_j` forcing-derivative norm escape on the full original sequence.
-/
theorem lowerTemporal_hilbertDerivativeNorm_escape_amplitude_or_forcingDerivative
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
                hH3 hClass j
                H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
                (τ (k n))
          )
          atTop
          atTop
    )
      ∨
    Tendsto
      (
        fun n : ℕ =>
          ‖deriv
            (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
              hH3 hClass j)
            (τ n)‖
      )
      atTop
      atTop := by

  rcases
    lowerTemporal_hilbertDerivativeNorm_escape_factor
      hH3 hClass j τ hτ hTauTendsto hLower
  with
    ⟨k, hk, hkTop, hTauK, hStateTop⟩
    |
    hForcingTop

  · left

    let X : ℕ → H3FourierComplexL2 :=
      fun n =>
        h3TerminalResolvedFourthTemporalHilbertState
          hH3 hClass j (τ (k n))

    have hStateTop' :
        Tendsto
          (fun n : ℕ => ‖X n‖)
          atTop
          atTop := by
      simpa only [X] using hStateTop

    have hSqTop :=
      tendsto_norm_sq_atTop_of_norm_tendstoAtTop
        X
        hStateTop'

    refine
      ⟨
        k,
        hk,
        hkTop,
        hTauK,
        ?_
      ⟩

    simpa only [
      X,
      resolvedFourthTemporalChannelAmplitude_eq_norm_sq_hilbertState
    ] using hSqTop

  · exact
      Or.inr hForcingTop

/--
Fourth-temporal Hilbert derivative escape is already normalized to its terminal
frontier: either the sixth-diffusion derivative norm escapes on a cofinal
subsequence, or the terminal `q² F_j` forcing derivative norm escapes on the
full original sequence.
-/
theorem fourthTemporal_hilbertDerivativeNorm_escape_sixth_or_forcingDerivative
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
    (hFourth :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
              (τ n)
        )
        atTop
        atTop) :
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
              h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
                hH3 hClass j
                H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
                (τ (k n))
          )
          atTop
          atTop
    )
      ∨
    Tendsto
      (
        fun n : ℕ =>
          ‖deriv
            (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
              hH3 hClass j)
            (τ n)‖
      )
      atTop
      atTop := by

  exact
    fourthTemporal_hilbertDerivativeNorm_escape_factor
      hH3 hClass j τ hτ hTauTendsto hFourth

end

end Euclidean
end Bridge
end PrimeTensor
