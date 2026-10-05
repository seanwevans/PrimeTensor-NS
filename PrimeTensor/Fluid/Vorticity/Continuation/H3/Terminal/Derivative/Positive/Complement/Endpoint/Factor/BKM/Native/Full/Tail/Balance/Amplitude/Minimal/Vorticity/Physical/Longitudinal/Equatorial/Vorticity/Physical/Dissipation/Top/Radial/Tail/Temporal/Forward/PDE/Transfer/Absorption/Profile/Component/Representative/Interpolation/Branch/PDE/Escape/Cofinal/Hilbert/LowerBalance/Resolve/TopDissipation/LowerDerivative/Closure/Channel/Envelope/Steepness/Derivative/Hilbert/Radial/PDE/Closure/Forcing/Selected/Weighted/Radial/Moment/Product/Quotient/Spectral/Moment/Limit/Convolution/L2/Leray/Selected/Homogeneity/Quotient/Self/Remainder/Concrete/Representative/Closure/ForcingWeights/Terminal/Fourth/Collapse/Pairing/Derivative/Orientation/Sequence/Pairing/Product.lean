import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing

/-!
# Hilbert product envelope for the resolved-channel pairing

The canonical oriented Hilbert pairing now tends to `+∞` along one fixed
resolved-channel terminal sequence.  Cauchy--Schwarz converts that signed
pairing escape into growth of the natural product of Hilbert-state magnitude
and Hilbert-state derivative magnitude.

For the three coordinate channels the product envelope is

    2 ‖X(t)‖ ‖X'(t)‖.

For top dissipation the canonical pairing is a finite coordinate sum, so the
uniform product envelope is

    ∑ k, 2 ‖V₄,k(t)‖ ‖V₄,k'(t)‖.

At every time,

    |pairing(channel,t)| ≤ productEnvelope(channel,t).

Hence the same terminal sequence has product envelope larger than `n` and
tending to `+∞`.

No inference is made yet that either factor separately diverges.
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
Natural Cauchy--Schwarz product envelope for one resolved physical PDE channel.
-/
noncomputable def h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (t : ℝ) :
    ℝ :=
  match channel with
  | .lowerTemporal =>
      2 *
        ‖h3TerminalResolvedLowerTemporalHilbertState
          hH3 hClass j t‖ *
        ‖deriv
          (h3TerminalResolvedLowerTemporalHilbertState
            hH3 hClass j)
          t‖
  | .topDissipation =>
      ∑ k : Fin 3,
        2 *
          ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass k t‖ *
          ‖deriv
            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass k)
            t‖
  | .fourthTemporal =>
      2 *
        ‖h3TerminalResolvedFourthTemporalHilbertState
          hH3 hClass j t‖ *
        ‖deriv
          (h3TerminalResolvedFourthTemporalHilbertState
            hH3 hClass j)
          t‖
  | .sixthDiffusion =>
      2 *
        ‖h3TerminalResolvedSixthDiffusionHilbertState
          hH3 hClass j t‖ *
        ‖deriv
          (h3TerminalResolvedSixthDiffusionHilbertState
            hH3 hClass j)
          t‖

private theorem abs_two_mul_real_inner_le_product
    (X D : H3FourierComplexL2) :
    abs (2 * inner ℝ X D)
      ≤
    2 * ‖X‖ * ‖D‖ := by

  calc
    abs (2 * inner ℝ X D)
        =
      2 * abs (inner ℝ X D) := by
        rw [abs_mul]
        norm_num
    _ ≤
      2 * (‖X‖ * ‖D‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (abs_real_inner_le_norm X D)
            (by norm_num)
    _ =
      2 * ‖X‖ * ‖D‖ := by
        ring

/--
The absolute canonical Hilbert pairing is bounded by the corresponding
channel-wise Hilbert product envelope.
-/
theorem abs_h3TerminalResolvedPhysicalPDEChannelHilbertPairing_le_productEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel) :
    abs
        (
          h3TerminalResolvedPhysicalPDEChannelHilbertPairing
            hH3 hClass j channel t
        )
      ≤
    h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope
      hH3 hClass j channel t := by

  cases channel with

  | lowerTemporal =>
      exact
        abs_two_mul_real_inner_le_product
          (
            h3TerminalResolvedLowerTemporalHilbertState
              hH3 hClass j t
          )
          (
            deriv
              (h3TerminalResolvedLowerTemporalHilbertState
                hH3 hClass j)
              t
          )

  | topDissipation =>

      let term : Fin 3 → ℝ :=
        fun k =>
          2 *
            inner ℝ
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass k t)
              (
                deriv
                  (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                    hH3 hClass k)
                  t
              )

      have hNormSum :
          ‖∑ k : Fin 3, term k‖
            ≤
          ∑ k : Fin 3, ‖term k‖ :=
        norm_sum_le
          (Finset.univ : Finset (Fin 3))
          term

      have hEach :
          ∑ k : Fin 3, ‖term k‖
            ≤
          ∑ k : Fin 3,
            2 *
              ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass k t‖ *
              ‖deriv
                (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass k)
                t‖ := by

        apply Finset.sum_le_sum

        intro k hk

        have hBound :=
          abs_two_mul_real_inner_le_product
            (
              h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass k t
            )
            (
              deriv
                (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass k)
                t
            )

        simpa only [
          term,
          Real.norm_eq_abs
        ] using hBound

      change
        abs (∑ k : Fin 3, term k)
          ≤
        ∑ k : Fin 3,
          2 *
            ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass k t‖ *
            ‖deriv
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass k)
              t‖

      rw [← Real.norm_eq_abs]

      exact
        le_trans
          hNormSum
          hEach

  | fourthTemporal =>
      exact
        abs_two_mul_real_inner_le_product
          (
            h3TerminalResolvedFourthTemporalHilbertState
              hH3 hClass j t
          )
          (
            deriv
              (h3TerminalResolvedFourthTemporalHilbertState
                hH3 hClass j)
              t
          )

  | sixthDiffusion =>
      exact
        abs_two_mul_real_inner_le_product
          (
            h3TerminalResolvedSixthDiffusionHilbertState
              hH3 hClass j t
          )
          (
            deriv
              (h3TerminalResolvedSixthDiffusionHilbertState
                hH3 hClass j)
              t
          )

/--
Under hypothetical nonextension, the same fixed resolved-channel terminal
sequence carries Hilbert product-envelope growth above `n`, and that product
envelope tends to `+∞`.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_hilbertProductEnvelopeEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T) :
    ∃ j₀ : Fin 3,
      ∃ channel : H3TerminalResolvedPhysicalPDEChannel,
        ∃ τ : ℕ → ℝ,
          (
            ∀ n : ℕ,
              τ n ∈ Set.Ioo a T
                ∧
              τ n ∈
                Set.Ioo
                  (T - (1 : ℝ) / ((n : ℝ) + 1))
                  T
                ∧
              (n : ℝ)
                <
              h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope
                hH3 hClass j₀ channel (τ n)
          )
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope
                  hH3 hClass j₀ channel (τ n)
            )
            atTop
            atTop := by

  obtain
    ⟨
      j₀,
      channel,
      s,
      τ,
      hτ,
      hTauTendsto,
      hPairTendsto
    ⟩ :=
    exists_fixed_oriented_resolvedPhysicalPDEChannel_hilbertPairingEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  have hProductData :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T
          ∧
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T
          ∧
        (n : ℝ)
          <
        h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope
          hH3 hClass j₀ channel (τ n) := by

    intro n

    have hOrientLeAbs :
        h3TerminalOrientedValue
            s
            (
              h3TerminalResolvedPhysicalPDEChannelHilbertPairing
                hH3 hClass j₀ channel (τ n)
            )
          ≤
        abs
          (
            h3TerminalResolvedPhysicalPDEChannelHilbertPairing
              hH3 hClass j₀ channel (τ n)
          ) :=
      h3TerminalOrientedValue_le_abs
        s
        (
          h3TerminalResolvedPhysicalPDEChannelHilbertPairing
            hH3 hClass j₀ channel (τ n)
        )

    have hAbsLeProduct :=
      abs_h3TerminalResolvedPhysicalPDEChannelHilbertPairing_le_productEnvelope
        (t := τ n)
        hH3 hClass j₀ channel

    exact
      ⟨
        (hτ n).1,
        (hτ n).2.1,
        lt_of_lt_of_le
          (lt_of_lt_of_le
            (hτ n).2.2
            hOrientLeAbs)
          hAbsLeProduct
      ⟩

  have hProductTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertProductEnvelope
              hH3 hClass j₀ channel (τ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    obtain
      ⟨N : ℕ, hN⟩ :=
      exists_nat_gt M

    filter_upwards
      [eventually_ge_atTop N]
      with n hn

    have hNn :
        (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn

    exact
      le_of_lt
        (
          lt_trans
            (lt_of_lt_of_le hN hNn)
            (hProductData n).2.2
        )

  exact
    ⟨
      j₀,
      channel,
      τ,
      hProductData,
      hTauTendsto,
      hProductTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
