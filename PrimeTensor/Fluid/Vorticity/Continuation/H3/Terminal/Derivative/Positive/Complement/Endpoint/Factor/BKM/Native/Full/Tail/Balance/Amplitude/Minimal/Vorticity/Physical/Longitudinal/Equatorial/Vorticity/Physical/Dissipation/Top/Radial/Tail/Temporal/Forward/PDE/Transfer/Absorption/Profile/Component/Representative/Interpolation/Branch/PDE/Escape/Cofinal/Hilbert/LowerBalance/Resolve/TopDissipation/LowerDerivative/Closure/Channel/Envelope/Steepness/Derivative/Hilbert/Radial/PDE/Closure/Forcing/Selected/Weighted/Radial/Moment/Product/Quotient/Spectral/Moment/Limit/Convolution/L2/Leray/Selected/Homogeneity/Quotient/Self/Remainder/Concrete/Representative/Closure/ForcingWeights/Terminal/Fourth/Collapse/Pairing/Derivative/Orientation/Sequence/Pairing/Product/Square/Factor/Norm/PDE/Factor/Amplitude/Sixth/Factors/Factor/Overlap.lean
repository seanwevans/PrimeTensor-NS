import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor

/-!
# Identify the selected eighth-radial velocity with terminal q⁴ velocity

The canonical terminal sixth-diffusion factorization is

    R₆,j = -V₄,j - F₃,j,

where `V₄,j = q⁴ û_j` and `F₃,j = q³ F_j`.

On every selected restart chart the same RHS is

    R₆,j = -(2π)^8 V8,j - (2π)^6 F6,j.

The selected forcing overlap already identifies

    (2π)^6 F6,j = F₃,j.

Cancelling this common forcing factor therefore gives the missing velocity
overlap

    (2π)^8 V8,j = V₄,j.

This confirms that the algebraically defined terminal fourth-q velocity is
exactly the local eighth-radial selected velocity on every admissible overlap.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1400000

theorem h3SelectedVelocityEighthRadialFourierL2OnSlab_eq_terminalVelocityFourthQ
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S a t₀ Q r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNS : LoggedPreterminalNavierStokesAdmissible u S)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ S E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u S t₀ hNS ht₀ hE hTail)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hrClass : r ∈ Set.Ioo a T)
    (hrS : r < S)
    (hrSlab : r - t₀ ∈ Set.Ioo (Q / 2) Q)
    (j : Fin 3) :
    ((2 * Real.pi) ^ 8 : ℝ) •
        h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
          8 (by norm_num)
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          (by positivity : 0 < Q / 2)
          hQR
          ⟨r - t₀, hrSlab.1.le, hrSlab.2.le⟩
          j
      =
    h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
      hH3 hClass hrClass j := by

  let s : Set.Icc (Q / 2) Q :=
    ⟨r - t₀, hrSlab.1.le, hrSlab.2.le⟩

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let hhalf : 0 < Q / 2 := by
    positivity

  let V8 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      8 (by norm_num)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hQR s j

  let F6 : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      6
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le j s

  have hRHS :=
    h3TerminalResolvedSixthDiffusionPDERHS_eq_selectedSixthDiffusionRHS
      hH3 hClass hNS ht₀ hE hTail hPhysical
      hQ hQR hrClass hrS hrSlab j

  have hForce :=
    h3SelectedForcingSixthQFourierL2OnSlab_eq_terminalForcingThirdQ
      hH3 hClass hNS ht₀ hE hTail hPhysical
      hQ hQR hrClass hrS
      ⟨hrSlab.1.le, hrSlab.2.le⟩
      j

  have hSplit :=
    h3TerminalResolvedSixthDiffusionPDERHS_eq_neg_velocityFourthQ_sub_forcingThirdQ
      hH3 hClass hrClass j

  change
    h3TerminalResolvedSixthDiffusionPDERHS
        hH3 hClass j r
      =
    (-((2 * Real.pi) ^ 8 : ℝ)) • V8
      -
    ((2 * Real.pi) ^ 6 : ℝ) • F6
    at hRHS

  change
    ((2 * Real.pi) ^ 6 : ℝ) • F6
      =
    h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
      hH3 hClass hrClass j
    at hForce

  rw [hSplit, hForce] at hRHS

  have hCancel :=
    congrArg
      (
        fun Z : H3FourierComplexL2 =>
          Z +
            h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
              hH3 hClass hrClass j
      )
      hRHS

  have hNeg :
      -
        h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
          hH3 hClass hrClass j
        =
      (-((2 * Real.pi) ^ 8 : ℝ)) • V8 := by

    simpa only [sub_add_cancel] using hCancel

  have hPos :
      h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
          hH3 hClass hrClass j
        =
      ((2 * Real.pi) ^ 8 : ℝ) • V8 := by

    simpa only [neg_smul, neg_inj] using hNeg

  dsimp only [V8, U₀, hA, hU₀, hhalf, s] at hPos ⊢

  exact hPos.symm

end

end Euclidean
end Bridge
end PrimeTensor
