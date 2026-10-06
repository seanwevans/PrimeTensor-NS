import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Freeze one terminal order-five radial product channel

The fourth-q forcing checkpoint reduces the remaining fourth-temporal
state-size forcing obstruction to escape of the explicit terminal order-four
radial Leray envelope.

That envelope is a finite sum over the nine pairs `(k,l) : Fin 3 × Fin 3` of
order-five radial raw-product-convolution norms.  At every time we choose a
pair maximizing those nine norms.  The complete Leray envelope is bounded by
one fixed positive numerical coefficient times that maximal pair norm.

Consequently envelope escape forces the chosen pair norm to escape.  Since the
pair type is finite, a cofinal extraction freezes one pair `(k,l)` while
preserving terminal convergence and divergence of its order-five radial
product-convolution norm.

This is a finite-channel reduction only; it introduces no new analytic
estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalFourthQForcingFixedRadialProductPair
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingFixedRadialProductPair :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Norm of one terminal order-five radial raw-product-convolution channel. -/
noncomputable def h3TerminalForcingFourthQRadialProductNormAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let h10 :
      ∀ q : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (U q) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
      hH3 hClass ht
  ‖h3RawProductConvolutionRadialFourierL2
      5
      (U k) (U l)
      (h10 k) (h10 l)‖

theorem h3TerminalForcingFourthQRadialProductNormAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    0 ≤
      h3TerminalForcingFourthQRadialProductNormAt
        hH3 hClass ht k l := by
  exact norm_nonneg _

/--
Universal coefficient obtained by bounding all nine order-five radial product
channels by one maximal pair in the fourth-q Leray envelope.
-/
noncomputable def h3TerminalForcingFourthQFixedPairCoefficient : ℝ :=
  ((2 * Real.pi) ^ 4 : ℝ) * 18 * (2 * Real.pi)

theorem h3TerminalForcingFourthQFixedPairCoefficient_pos :
    0 < h3TerminalForcingFourthQFixedPairCoefficient := by
  unfold h3TerminalForcingFourthQFixedPairCoefficient
  positivity

/--
Rewrite the named fourth-q radial-Leray envelope directly in terms of the
terminal order-five product norms.
-/
theorem h3TerminalForcingFourthQRadialLerayEnvelopeAt_eq_sum_productNorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalForcingFourthQRadialLerayEnvelopeAt
        hH3 hClass ht j
      =
    ((2 * Real.pi) ^ 4 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                h3TerminalForcingFourthQRadialProductNormAt
                  hH3 hClass ht k l
          )
    ) := by
  rfl

/--
At each strict terminal time, the full fourth-q radial-Leray envelope is
bounded by one universal positive coefficient times one of its nine order-five
radial product channels.
-/
theorem exists_pair_h3TerminalForcingFourthQRadialLerayEnvelopeAt_le_fixedCoefficient_mul_productNorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ∃ k l : Fin 3,
      h3TerminalForcingFourthQRadialLerayEnvelopeAt
          hH3 hClass ht j
        ≤
      h3TerminalForcingFourthQFixedPairCoefficient
        *
      h3TerminalForcingFourthQRadialProductNormAt
        hH3 hClass ht k l := by

  classical

  let f : Fin 3 × Fin 3 → ℝ :=
    fun p =>
      h3TerminalForcingFourthQRadialProductNormAt
        hH3 hClass ht p.1 p.2

  have hUnivNonempty :
      (Finset.univ : Finset (Fin 3 × Fin 3)).Nonempty := by
    exact
      ⟨
        (0, 0),
        Finset.mem_univ _
      ⟩

  obtain
    ⟨p, _hpMem, hpMax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (Fin 3 × Fin 3))
      f
      hUnivNonempty

  refine
    ⟨
      p.1,
      p.2,
      ?_
    ⟩

  have hInner :
      ∀ k : Fin 3,
        (
          ∑ l : Fin 3,
            (2 * Real.pi) * f (k, l)
        )
          ≤
        3 * ((2 * Real.pi) * f p) := by

    intro k

    calc
      (
        ∑ l : Fin 3,
          (2 * Real.pi) * f (k, l)
      )
          ≤
        ((Finset.univ : Finset (Fin 3)).card : ℕ)
          •
        ((2 * Real.pi) * f p) := by

            exact
              Finset.sum_le_card_nsmul
                (Finset.univ : Finset (Fin 3))
                (fun l : Fin 3 =>
                  (2 * Real.pi) * f (k, l))
                ((2 * Real.pi) * f p)
                (fun l hl =>
                  mul_le_mul_of_nonneg_left
                    (
                      hpMax
                        (k, l)
                        (Finset.mem_univ _)
                    )
                    (by positivity))

      _ = 3 * ((2 * Real.pi) * f p) := by
            norm_num [nsmul_eq_mul]

  have hOuter :
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) * f (k, l)
            )
      )
        ≤
      3 *
        (
          2 *
            (
              3 * ((2 * Real.pi) * f p)
            )
        ) := by

    calc
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) * f (k, l)
            )
      )
          ≤
        ((Finset.univ : Finset (Fin 3)).card : ℕ)
          •
        (
          2 *
            (
              3 * ((2 * Real.pi) * f p)
            )
        ) := by

            exact
              Finset.sum_le_card_nsmul
                (Finset.univ : Finset (Fin 3))
                (fun k : Fin 3 =>
                  2 *
                    (
                      ∑ l : Fin 3,
                        (2 * Real.pi) * f (k, l)
                    ))
                (
                  2 *
                    (
                      3 * ((2 * Real.pi) * f p)
                    )
                )
                (fun k hk =>
                  mul_le_mul_of_nonneg_left
                    (hInner k)
                    (by norm_num))

      _ =
        3 *
          (
            2 *
              (
                3 * ((2 * Real.pi) * f p)
              )
          ) := by
            norm_num [nsmul_eq_mul]

  rw [
    h3TerminalForcingFourthQRadialLerayEnvelopeAt_eq_sum_productNorm
      hH3 hClass ht j
  ]

  change
    ((2 * Real.pi) ^ 4 : ℝ)
        *
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) * f (k, l)
            )
      )
      ≤
    h3TerminalForcingFourthQFixedPairCoefficient
      *
    f p

  calc
    ((2 * Real.pi) ^ 4 : ℝ)
        *
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) * f (k, l)
            )
      )
        ≤
      ((2 * Real.pi) ^ 4 : ℝ)
        *
      (
        3 *
          (
            2 *
              (
                3 * ((2 * Real.pi) * f p)
              )
          )
      ) := by
        exact
          mul_le_mul_of_nonneg_left
            hOuter
            (by positivity)

    _ =
      h3TerminalForcingFourthQFixedPairCoefficient
        *
      f p := by
        unfold h3TerminalForcingFourthQFixedPairCoefficient
        ring

/--
If the fourth-q radial-Leray envelope diverges along a terminal sequence, a
cofinal subsequence freezes one pair `(k,l)` whose order-five radial
product-convolution norm also diverges.
-/
theorem exists_fixed_pair_subsequence_of_h3TerminalForcingFourthQRadialLerayEnvelopeAt_tendstoAtTop
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
    (hEnvelopeTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQRadialLerayEnvelopeAt
              hH3 hClass (hτ n) j
        )
        atTop
        atTop) :
    ∃ k l : Fin 3,
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
              h3TerminalForcingFourthQRadialProductNormAt
                hH3 hClass (hτ (s n)) k l
          )
          atTop
          atTop := by

  classical

  have hChoice :
      ∀ n : ℕ,
        ∃ p : Fin 3 × Fin 3,
          h3TerminalForcingFourthQRadialLerayEnvelopeAt
              hH3 hClass (hτ n) j
            ≤
          h3TerminalForcingFourthQFixedPairCoefficient
            *
          h3TerminalForcingFourthQRadialProductNormAt
            hH3 hClass (hτ n) p.1 p.2 := by

    intro n

    obtain
      ⟨k, l, hkl⟩ :=
      exists_pair_h3TerminalForcingFourthQRadialLerayEnvelopeAt_le_fixedCoefficient_mul_productNorm
        hH3 hClass (hτ n) j

    exact
      ⟨
        (k, l),
        hkl
      ⟩

  choose p hp using hChoice

  have hCPos :
      0 < h3TerminalForcingFourthQFixedPairCoefficient :=
    h3TerminalForcingFourthQFixedPairCoefficient_pos

  have hChosenTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hτ n) (p n).1 (p n).2
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    let M0 : ℝ :=
      max M 0

    have hMLe :
        M ≤ M0 := by
      dsimp only [M0]
      exact le_max_left M 0

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          h3TerminalForcingFourthQFixedPairCoefficient * M0
            <
          h3TerminalForcingFourthQRadialLerayEnvelopeAt
            hH3 hClass (hτ n) j :=
      hEnvelopeTop.eventually
        (
          eventually_gt_atTop
            (
              h3TerminalForcingFourthQFixedPairCoefficient * M0
            )
        )

    filter_upwards [hLarge] with n hn

    have hBound :=
      hp n

    have hScaled :
        h3TerminalForcingFourthQFixedPairCoefficient * M0
          <
        h3TerminalForcingFourthQFixedPairCoefficient
          *
        h3TerminalForcingFourthQRadialProductNormAt
          hH3 hClass (hτ n) (p n).1 (p n).2 :=
      lt_of_lt_of_le
        hn
        hBound

    have hM0Lt :
        M0
          <
        h3TerminalForcingFourthQRadialProductNormAt
          hH3 hClass (hτ n) (p n).1 (p n).2 := by

      by_contra hNot

      have hReverse :
          h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hτ n) (p n).1 (p n).2
            ≤
          M0 :=
        le_of_not_gt hNot

      have hScaledReverse :
          h3TerminalForcingFourthQFixedPairCoefficient
              *
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hτ n) (p n).1 (p n).2
            ≤
          h3TerminalForcingFourthQFixedPairCoefficient * M0 :=
        mul_le_mul_of_nonneg_left
          hReverse
          hCPos.le

      exact
        (not_lt_of_ge hScaledReverse)
          hScaled

    exact
      le_of_lt
        (
          lt_of_le_of_lt
            hMLe
            hM0Lt
        )

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q : Fin 3 × Fin 3,
          p n = q :=
    Frequently.of_forall
      (
        fun n =>
          ⟨
            p n,
            rfl
          ⟩
      )

  obtain
    ⟨q, hFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySome

  obtain
    ⟨s, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop
      hFrequently

  have hs :
      ∀ n : ℕ,
        n ≤ s n := by
    intro n
    exact hMono.le_apply

  have hsTop :
      Tendsto s atTop atTop :=
    hMono.tendsto_atTop

  have hTauSub :
      Tendsto
        (fun n : ℕ => τ (s n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp
      hsTop

  have hPairTopBeforeRewrite :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass
              (hτ (s n))
              (p (s n)).1
              (p (s n)).2
        )
        atTop
        atTop :=
    hChosenTop.comp
      hsTop

  have hPairTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass
              (hτ (s n))
              q.1
              q.2
        )
        atTop
        atTop := by

    simpa only [hFixed] using
      hPairTopBeforeRewrite

  exact
    ⟨
      q.1,
      q.2,
      s,
      hs,
      hsTop,
      hTauSub,
      hPairTop
    ⟩

/--
The fourth-temporal state-amplitude frontier now reduces to either the existing
shift-two higher-radial velocity moment, or one fixed terminal order-five
radial raw-product-convolution channel on a cofinal subsequence.
-/
theorem fourthTemporal_amplitude_escape_extendedHigherTwo_or_fixedForcingRadialProductPair
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
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass 2
                (τ (s n))
                (hτ (s n))
          )
          atTop
          (𝓝 ∞)
    )
      ∨
    (
      ∃ k l : Fin 3,
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
                h3TerminalForcingFourthQRadialProductNormAt
                  hH3 hClass (hτ (s n)) k l
            )
            atTop
            atTop
    ) := by

  rcases
    fourthTemporal_amplitude_escape_extendedHigherTwo_or_forcingFourthQRadialLerayEnvelope
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop
  with
    hHigher
    |
    hEnvelope

  · exact
      Or.inl hHigher

  · rcases hEnvelope with
      ⟨r, hr, hrTop, hTauR, hEnvelopeTop⟩

    obtain
      ⟨k, l, s, hs, hsTop, hTauRS, hPairTop⟩ :=
      exists_fixed_pair_subsequence_of_h3TerminalForcingFourthQRadialLerayEnvelopeAt_tendstoAtTop
        hH3 hClass j
        (fun n : ℕ => τ (r n))
        (fun n : ℕ => hτ (r n))
        hTauR
        hEnvelopeTop

    let q : ℕ → ℕ :=
      fun n => r (s n)

    have hq :
        ∀ n : ℕ,
          n ≤ q n := by
      intro n
      exact
        (hs n).trans
          (hr (s n))

    have hqTop :
        Tendsto q atTop atTop := by
      dsimp only [q]
      exact
        hrTop.comp
          hsTop

    have hTauQ :
        Tendsto
          (fun n : ℕ => τ (q n))
          atTop
          (𝓝 T) := by
      dsimp only [q]
      exact hTauRS

    have hPairQ :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingFourthQRadialProductNormAt
                hH3 hClass (hτ (q n)) k l
          )
          atTop
          atTop := by
      dsimp only [q]
      exact hPairTop

    exact
      Or.inr
        ⟨
          k,
          l,
          q,
          hq,
          hqTop,
          hTauQ,
          hPairQ
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
