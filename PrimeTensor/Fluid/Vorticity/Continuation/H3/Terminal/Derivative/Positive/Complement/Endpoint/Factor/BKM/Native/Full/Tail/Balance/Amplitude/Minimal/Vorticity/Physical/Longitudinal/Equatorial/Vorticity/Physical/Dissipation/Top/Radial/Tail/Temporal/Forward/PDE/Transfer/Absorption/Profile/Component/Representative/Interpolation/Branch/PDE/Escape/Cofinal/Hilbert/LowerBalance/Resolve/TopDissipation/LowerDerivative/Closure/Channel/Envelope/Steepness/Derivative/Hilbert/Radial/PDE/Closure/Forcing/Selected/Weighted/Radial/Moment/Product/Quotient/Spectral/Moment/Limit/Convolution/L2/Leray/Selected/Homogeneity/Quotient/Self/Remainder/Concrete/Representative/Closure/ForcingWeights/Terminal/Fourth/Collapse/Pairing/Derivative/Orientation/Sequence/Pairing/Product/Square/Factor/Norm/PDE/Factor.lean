import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Tail.Cascade

/-!
# Split the next resolved Hilbert PDE derivative factors

The preceding checkpoint identifies the two next-order PDE right-hand sides

    X₁' = -X₂ - (q F)',
    X₂' = -X₃' - (q² F)'.

This file uses only the triangle inequality and the existing cofinal-tail
extraction to resolve norm escape of those sums into their actual factors.

Thus:

* lower-temporal derivative-norm escape is carried either by the
  fourth-temporal state norm `‖X₂‖` on a cofinal subsequence, or by the forcing
  derivative norm `‖(q F)'‖` along the original sequence;
* fourth-temporal derivative-norm escape is carried either by the
  sixth-diffusion derivative norm `‖X₃'‖` on a cofinal subsequence, or by the
  forcing derivative norm `‖(q² F)'‖` along the original sequence.

The alternatives are deliberately exhaustive and asymmetric: if the first
factor is eventually bounded, the second factor diverges on the full original
sequence; otherwise the first factor is extracted cofinally.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1400000

/-! ## Generic two-factor sequence split -/

/--
A real sequence is either eventually bounded above or has a cofinal extraction
tending to `+∞`.
-/
private theorem eventuallyBounded_or_cofinalTendstoAtTop_factorPDE
    (f : ℕ → ℝ) :
    (
      ∃ C : ℝ,
        ∀ᶠ n : ℕ in atTop,
          f n ≤ C
    )
      ∨
    (
      ∃ k : ℕ → ℕ,
        (∀ n : ℕ, n ≤ k n)
          ∧
        Tendsto k atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => f (k n))
          atTop
          atTop
    ) := by

  have hIdentity :
      ∀ᶠ n : ℕ in atTop,
        (1 + f n : ℝ) = 1 + f n :=
    Eventually.of_forall
      (fun _ => rfl)

  have hTail :=
    relativeTailAlternative_of_eventually_ratio_identity
      f
      (fun n => 1 + f n)
      hIdentity

  unfold H3TerminalRelativeTailAlternative at hTail

  rcases hTail with
    ⟨C, hBound⟩
    |
    ⟨k, hk, hkTop, hfTop, hRatioTop⟩

  · exact
      Or.inl
        ⟨
          C,
          hBound.mono
            (fun n hn => hn.1)
        ⟩

  · exact
      Or.inr
        ⟨
          k,
          (fun n => (hk n).1),
          hkTop,
          hfTop
        ⟩

/--
If `A + B -> +∞`, then either `A` has a cofinal extraction tending to `+∞`,
or `B -> +∞` along the full original sequence.
-/
private theorem exists_cofinal_left_or_right_tendstoAtTop_of_add_tendstoAtTop
    (A B : ℕ → ℝ)
    (hAdd :
      Tendsto
        (fun n : ℕ => A n + B n)
        atTop
        atTop) :
    (
      ∃ k : ℕ → ℕ,
        (∀ n : ℕ, n ≤ k n)
          ∧
        Tendsto k atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => A (k n))
          atTop
          atTop
    )
      ∨
    Tendsto B atTop atTop := by

  rcases
    eventuallyBounded_or_cofinalTendstoAtTop_factorPDE A
  with
    ⟨C, hABound⟩
    |
    ⟨k, hk, hkTop, hATop⟩

  · right

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hAddLarge :
        ∀ᶠ n : ℕ in atTop,
          M + C
            ≤
          A n + B n :=
      (tendsto_atTop.1 hAdd)
        (M + C)

    filter_upwards
      [hABound, hAddLarge]
      with n hAn hLarge

    linarith

  · exact
      Or.inl
        ⟨
          k,
          hk,
          hkTop,
          hATop
        ⟩

/-! ## Lower-temporal factor split -/

/--
If the lower-temporal Hilbert derivative norm diverges along a strict terminal
sequence, then either the fourth-temporal Hilbert-state norm diverges on a
cofinal subsequence, or the canonical `q F_j` forcing derivative norm diverges
along the full original sequence.
-/
theorem lowerTemporal_hilbertDerivativeNorm_escape_factor
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
              ‖h3TerminalResolvedFourthTemporalHilbertState
                hH3 hClass j (τ (k n))‖
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

  let A : ℕ → ℝ :=
    fun n =>
      ‖h3TerminalResolvedFourthTemporalHilbertState
        hH3 hClass j (τ n)‖

  let B : ℕ → ℝ :=
    fun n =>
      ‖deriv
        (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
          hH3 hClass j)
        (τ n)‖

  have hAdd :
      Tendsto
        (fun n : ℕ => A n + B n)
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          M
            ≤
          h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
            (τ n) :=
      (tendsto_atTop.1 hLower) M

    filter_upwards
      [hLarge]
      with n hn

    have hEq :=
      h3TerminalResolvedLowerTemporalHilbertDerivativeNormEnvelope_eq_norm_pdeRHS
        hH3 hClass (hτ n) j

    have hTri :
        ‖h3TerminalResolvedLowerTemporalHilbertDerivativePDERHS
            hH3 hClass j (τ n)‖
          ≤
        A n + B n := by

      unfold
        h3TerminalResolvedLowerTemporalHilbertDerivativePDERHS

      dsimp only [A, B]

      simpa only [norm_neg] using
        norm_sub_le
          (-
            h3TerminalResolvedFourthTemporalHilbertState
              hH3 hClass j (τ n))
          (
            deriv
              (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
                hH3 hClass j)
              (τ n)
          )

    exact
      le_trans
        (by simpa only [hEq] using hn)
        hTri

  rcases
    exists_cofinal_left_or_right_tendstoAtTop_of_add_tendstoAtTop
      A B hAdd
  with
    ⟨k, hk, hkTop, hATop⟩
    |
    hBTop

  · left

    exact
      ⟨
        k,
        hk,
        hkTop,
        hTauTendsto.comp hkTop,
        by simpa only [A] using hATop
      ⟩

  · right

    simpa only [B] using hBTop

/-! ## Fourth-temporal factor split -/

/--
If the fourth-temporal Hilbert derivative norm diverges along a strict terminal
sequence, then either the sixth-diffusion Hilbert derivative norm diverges on a
cofinal subsequence, or the canonical `q² F_j` forcing derivative norm diverges
along the full original sequence.
-/
theorem fourthTemporal_hilbertDerivativeNorm_escape_factor
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

  let A : ℕ → ℝ :=
    fun n =>
      ‖deriv
        (h3TerminalResolvedSixthDiffusionHilbertState
          hH3 hClass j)
        (τ n)‖

  let B : ℕ → ℝ :=
    fun n =>
      ‖deriv
        (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j)
        (τ n)‖

  have hAdd :
      Tendsto
        (fun n : ℕ => A n + B n)
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          M
            ≤
          h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
            (τ n) :=
      (tendsto_atTop.1 hFourth) M

    filter_upwards
      [hLarge]
      with n hn

    have hEq :=
      h3TerminalResolvedFourthTemporalHilbertDerivativeNormEnvelope_eq_norm_pdeRHS
        hH3 hClass (hτ n) j

    have hTri :
        ‖h3TerminalResolvedFourthTemporalHilbertDerivativePDERHS
            hH3 hClass j (τ n)‖
          ≤
        A n + B n := by

      unfold
        h3TerminalResolvedFourthTemporalHilbertDerivativePDERHS

      dsimp only [A, B]

      simpa only [norm_neg] using
        norm_sub_le
          (-
            deriv
              (h3TerminalResolvedSixthDiffusionHilbertState
                hH3 hClass j)
              (τ n))
          (
            deriv
              (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
                hH3 hClass j)
              (τ n)
          )

    exact
      le_trans
        (by simpa only [hEq] using hn)
        hTri

  rcases
    exists_cofinal_left_or_right_tendstoAtTop_of_add_tendstoAtTop
      A B hAdd
  with
    ⟨k, hk, hkTop, hATop⟩
    |
    hBTop

  · left

    refine
      ⟨
        k,
        hk,
        hkTop,
        hTauTendsto.comp hkTop,
        ?_
      ⟩

    simpa only [
      A,
      h3TerminalResolvedSixthDiffusionHilbertDerivativeNormEnvelope_eq
    ] using hATop

  · right

    simpa only [B] using hBTop

end

end Euclidean
end Bridge
end PrimeTensor
