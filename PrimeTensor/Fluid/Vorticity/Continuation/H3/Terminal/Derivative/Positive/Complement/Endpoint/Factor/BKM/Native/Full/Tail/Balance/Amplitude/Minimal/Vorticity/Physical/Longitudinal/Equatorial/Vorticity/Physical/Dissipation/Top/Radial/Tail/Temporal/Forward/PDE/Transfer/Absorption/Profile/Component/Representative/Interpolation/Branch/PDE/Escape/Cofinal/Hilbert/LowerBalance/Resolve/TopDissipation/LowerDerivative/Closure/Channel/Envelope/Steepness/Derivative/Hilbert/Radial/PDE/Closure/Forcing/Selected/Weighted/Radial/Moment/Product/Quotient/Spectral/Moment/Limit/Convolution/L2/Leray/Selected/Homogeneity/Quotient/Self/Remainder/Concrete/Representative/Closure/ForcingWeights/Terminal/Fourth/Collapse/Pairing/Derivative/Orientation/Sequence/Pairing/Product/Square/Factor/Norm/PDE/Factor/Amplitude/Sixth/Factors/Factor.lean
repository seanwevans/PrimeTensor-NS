import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Tail.Cascade

/-!
# Split terminal sixth-diffusion escape into q⁴ velocity or q³ forcing

The canonical terminal sixth-diffusion right-hand side has now been resolved
exactly as

    R₆,j(t) = - V₄,j(t) - F₃,j(t),

where

    V₄,j = q⁴ û_j,
    F₃,j = q³ F_j

are genuine canonical terminal Fourier `L²` states.

Therefore norm escape of the sixth-diffusion Hilbert derivative has only two
remaining carriers.  By the triangle inequality and the standard cofinal-tail
extraction:

* either `‖V₄,j‖ -> +∞` on a cofinal subsequence;
* or `‖F₃,j‖ -> +∞` along the full original terminal sequence.

No preference is imposed between the two branches.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1400000

/--
A real sequence is either eventually bounded above or admits a cofinal
extraction tending to `+∞`.
-/
private theorem eventuallyBounded_or_cofinalTendstoAtTop_sixthFactor
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
private theorem exists_cofinal_left_or_right_tendstoAtTop_of_add_tendstoAtTop_sixthFactor
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
    eventuallyBounded_or_cofinalTendstoAtTop_sixthFactor A
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

/--
If the sixth-diffusion Hilbert derivative norm diverges along a strict
terminal sequence, then either the canonical terminal `q⁴ û_j` velocity norm
diverges on a cofinal subsequence, or the canonical terminal `q³ F_j` forcing
norm diverges along the full original sequence.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_velocityFourthQ_or_forcingThirdQ
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
              ‖h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
                hH3 hClass (hτ (k n)) j‖
          )
          atTop
          atTop
    )
      ∨
    Tendsto
      (
        fun n : ℕ =>
          ‖h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
            hH3 hClass (hτ n) j‖
      )
      atTop
      atTop := by

  let A : ℕ → ℝ :=
    fun n =>
      ‖h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
        hH3 hClass (hτ n) j‖

  let B : ℕ → ℝ :=
    fun n =>
      ‖h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
        hH3 hClass (hτ n) j‖

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
            H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
            (τ n) :=
      (tendsto_atTop.1 hSixth) M

    filter_upwards
      [hLarge]
      with n hn

    have hNormEq :=
      h3TerminalResolvedSixthDiffusionHilbertDerivativeNormEnvelope_eq_norm_pdeRHS
        (t := τ n)
        hH3 hClass j

    have hSplit :=
      h3TerminalResolvedSixthDiffusionPDERHS_eq_neg_velocityFourthQ_sub_forcingThirdQ
        hH3 hClass (hτ n) j

    have hTri :
        ‖h3TerminalResolvedSixthDiffusionPDERHS
            hH3 hClass j (τ n)‖
          ≤
        A n + B n := by

      rw [hSplit]

      dsimp only [A, B]

      simpa only [norm_neg] using
        norm_sub_le
          (-
            h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
              hH3 hClass (hτ n) j)
          (
            h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
              hH3 hClass (hτ n) j
          )

    have hRHSBig :
        M
          ≤
        ‖h3TerminalResolvedSixthDiffusionPDERHS
          hH3 hClass j (τ n)‖ := by

      rw [hNormEq] at hn
      exact hn

    exact
      le_trans
        hRHSBig
        hTri

  rcases
    exists_cofinal_left_or_right_tendstoAtTop_of_add_tendstoAtTop_sixthFactor
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

    simpa only [A] using hATop

  · right

    simpa only [B] using hBTop

end

end Euclidean
end Bridge
end PrimeTensor
