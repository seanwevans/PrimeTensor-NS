import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.SecondQ
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Freeze second-q forcing-state escape into one radial product pair

The preceding checkpoint bounds the canonical terminal second-q forcing state

    q F_j(U,U)

by the order-two radial Leray envelope.  This file performs the first finite
extraction step.

The envelope is a finite sum of order-three product-convolution norms.  If the
second-q forcing mass diverges on a terminal sequence, then the radial Leray
envelope diverges, and one fixed coordinate pair `(k,l)` carries an
order-three product-convolution norm escape on a cofinal subsequence.

No primitive velocity mass is classified here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSecondQForcingStateEscape
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalSecondQForcingStateEscape :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 2200000

/-! ## Named order-two radial Leray envelope -/

noncomputable def h3TerminalForcingSecondQRadialLerayEnvelopeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let h6 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (2 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
      hH3 hClass ht
  ((2 * Real.pi) ^ 2 : ℝ)
    *
  (
    ∑ k : Fin 3,
      2 *
        (
          ∑ l : Fin 3,
            (2 * Real.pi) *
              ‖h3RawProductConvolutionRadialFourierL2
                  3
                  (U k) (U l)
                  (h6 k) (h6 l)‖
        )
  )

theorem h3TerminalForcingSecondQRadialLerayEnvelopeAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    0 ≤
      h3TerminalForcingSecondQRadialLerayEnvelopeAt
        hH3 hClass ht j := by

  unfold h3TerminalForcingSecondQRadialLerayEnvelopeAt
  dsimp only

  apply mul_nonneg
  · positivity

  apply Finset.sum_nonneg
  intro k hk

  apply mul_nonneg
  · norm_num

  apply Finset.sum_nonneg
  intro l hl

  exact
    mul_nonneg
      (by positivity)
      (norm_nonneg _)

theorem h3TerminalPhysicalTopDissipationForcingSecondQMassAt_le_sq_radialLerayEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingSecondQMassAt
        hH3 hClass ht j
      ≤
    (
      h3TerminalForcingSecondQRadialLerayEnvelopeAt
        hH3 hClass ht j
    ) ^ 2 := by

  simpa only [h3TerminalForcingSecondQRadialLerayEnvelopeAt] using
    h3TerminalPhysicalTopDissipationForcingSecondQMassAt_le_sq_radialLeray
      hH3 hClass ht j

theorem h3TerminalForcingSecondQRadialLerayEnvelopeAt_tendstoAtTop_of_massPath_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hMassTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalPhysicalTopDissipationForcingSecondQMassPath
            hH3 hClass j (τ n))
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalForcingSecondQRadialLerayEnvelopeAt
          hH3 hClass (hτ n) j)
      atTop atTop := by

  have hAtTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalPhysicalTopDissipationForcingSecondQMassAt
            hH3 hClass (hτ n) j)
        atTop atTop := by

    have hEq :
        (fun n : ℕ =>
          h3TerminalPhysicalTopDissipationForcingSecondQMassPath
            hH3 hClass j (τ n))
          =
        (fun n : ℕ =>
          h3TerminalPhysicalTopDissipationForcingSecondQMassAt
            hH3 hClass (hτ n) j) := by

      funext n

      exact
        h3TerminalPhysicalTopDissipationForcingSecondQMassPath_eq
          hH3 hClass (hτ n) j

    rw [hEq] at hMassTop

    exact hMassTop

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ := max M 0

  have hMLe :
      M ≤ R := by
    dsimp only [R]
    exact le_max_left M 0

  have hR0 :
      0 ≤ R := by
    dsimp only [R]
    exact le_max_right M 0

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        R ^ 2
          <
        h3TerminalPhysicalTopDissipationForcingSecondQMassAt
          hH3 hClass (hτ n) j :=
    hAtTop.eventually
      (eventually_gt_atTop (R ^ 2))

  filter_upwards [hLarge] with n hn

  have hBound :=
    h3TerminalPhysicalTopDissipationForcingSecondQMassAt_le_sq_radialLerayEnvelope
      hH3 hClass (hτ n) j

  have hEnv0 :=
    h3TerminalForcingSecondQRadialLerayEnvelopeAt_nonneg
      hH3 hClass (hτ n) j

  have hRLt :
      R
        <
      h3TerminalForcingSecondQRadialLerayEnvelopeAt
        hH3 hClass (hτ n) j := by
    nlinarith

  exact
    hMLe.trans
      (le_of_lt hRLt)

/-! ## Freeze one order-three convolution pair -/

noncomputable def h3TerminalForcingSecondQRadialProductNormAt
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
  let h6 :
      ∀ q : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (2 + 1) : ℕ) : ℝ))
          (U q) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
      hH3 hClass ht
  ‖h3RawProductConvolutionRadialFourierL2
      3
      (U k) (U l)
      (h6 k) (h6 l)‖

theorem h3TerminalForcingSecondQRadialProductNormAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    0 ≤
      h3TerminalForcingSecondQRadialProductNormAt
        hH3 hClass ht k l :=
  norm_nonneg _

noncomputable def h3TerminalForcingSecondQFixedPairCoefficient : ℝ :=
  ((2 * Real.pi) ^ 2 : ℝ) * 18 * (2 * Real.pi)

theorem h3TerminalForcingSecondQFixedPairCoefficient_pos :
    0 < h3TerminalForcingSecondQFixedPairCoefficient := by
  unfold h3TerminalForcingSecondQFixedPairCoefficient
  positivity

theorem h3TerminalForcingSecondQRadialLerayEnvelopeAt_eq_sum_productNorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalForcingSecondQRadialLerayEnvelopeAt
        hH3 hClass ht j
      =
    ((2 * Real.pi) ^ 2 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                h3TerminalForcingSecondQRadialProductNormAt
                  hH3 hClass ht k l
          )
    ) := by
  rfl

theorem exists_pair_h3TerminalForcingSecondQRadialLerayEnvelopeAt_le_fixedCoefficient_mul_productNorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ∃ k l : Fin 3,
      h3TerminalForcingSecondQRadialLerayEnvelopeAt
          hH3 hClass ht j
        ≤
      h3TerminalForcingSecondQFixedPairCoefficient
        *
      h3TerminalForcingSecondQRadialProductNormAt
        hH3 hClass ht k l := by

  classical

  let f : Fin 3 × Fin 3 → ℝ :=
    fun p =>
      h3TerminalForcingSecondQRadialProductNormAt
        hH3 hClass ht p.1 p.2

  have hUnivNonempty :
      (Finset.univ : Finset (Fin 3 × Fin 3)).Nonempty :=
    ⟨(0, 0), Finset.mem_univ _⟩

  obtain ⟨p, _hpMem, hpMax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (Fin 3 × Fin 3))
      f
      hUnivNonempty

  refine ⟨p.1, p.2, ?_⟩

  have hInner :
      ∀ k : Fin 3,
        (∑ l : Fin 3, (2 * Real.pi) * f (k, l))
          ≤
        3 * ((2 * Real.pi) * f p) := by

    intro k

    calc
      (∑ l : Fin 3, (2 * Real.pi) * f (k, l))
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
                    (hpMax (k, l) (Finset.mem_univ _))
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
    h3TerminalForcingSecondQRadialLerayEnvelopeAt_eq_sum_productNorm
      hH3 hClass ht j
  ]

  change
    ((2 * Real.pi) ^ 2 : ℝ)
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
    h3TerminalForcingSecondQFixedPairCoefficient
      *
    f p

  calc
    ((2 * Real.pi) ^ 2 : ℝ)
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
      ((2 * Real.pi) ^ 2 : ℝ)
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
      h3TerminalForcingSecondQFixedPairCoefficient
        *
      f p := by
        unfold h3TerminalForcingSecondQFixedPairCoefficient
        ring

theorem exists_fixed_pair_subsequence_of_h3TerminalForcingSecondQMassPath_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMassTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalPhysicalTopDissipationForcingSecondQMassPath
            hH3 hClass j (τ n))
        atTop atTop) :
    ∃ k l : Fin 3,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingSecondQRadialProductNormAt
              hH3 hClass (hτ (s n)) k l)
          atTop atTop := by

  classical

  have hEnvelopeTop :=
    h3TerminalForcingSecondQRadialLerayEnvelopeAt_tendstoAtTop_of_massPath_tendstoAtTop
      hH3 hClass j τ hτ hMassTop

  have hChoice :
      ∀ n : ℕ,
        ∃ p : Fin 3 × Fin 3,
          h3TerminalForcingSecondQRadialLerayEnvelopeAt
              hH3 hClass (hτ n) j
            ≤
          h3TerminalForcingSecondQFixedPairCoefficient
            *
          h3TerminalForcingSecondQRadialProductNormAt
            hH3 hClass (hτ n) p.1 p.2 := by

    intro n

    obtain ⟨k, l, hkl⟩ :=
      exists_pair_h3TerminalForcingSecondQRadialLerayEnvelopeAt_le_fixedCoefficient_mul_productNorm
        hH3 hClass (hτ n) j

    exact ⟨(k, l), hkl⟩

  choose p hp using hChoice

  have hCPos :
      0 < h3TerminalForcingSecondQFixedPairCoefficient :=
    h3TerminalForcingSecondQFixedPairCoefficient_pos

  have hChosenTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingSecondQRadialProductNormAt
            hH3 hClass (hτ n) (p n).1 (p n).2)
        atTop atTop := by

    refine tendsto_atTop.2 ?_

    intro M

    let R : ℝ := max M 0

    have hMLe :
        M ≤ R := by
      dsimp only [R]
      exact le_max_left M 0

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          h3TerminalForcingSecondQFixedPairCoefficient * R
            <
          h3TerminalForcingSecondQRadialLerayEnvelopeAt
            hH3 hClass (hτ n) j :=
      hEnvelopeTop.eventually
        (eventually_gt_atTop
          (h3TerminalForcingSecondQFixedPairCoefficient * R))

    filter_upwards [hLarge] with n hn

    have hBound := hp n

    have hScaled :
        h3TerminalForcingSecondQFixedPairCoefficient * R
          <
        h3TerminalForcingSecondQFixedPairCoefficient
          *
        h3TerminalForcingSecondQRadialProductNormAt
          hH3 hClass (hτ n) (p n).1 (p n).2 :=
      lt_of_lt_of_le hn hBound

    have hRLt :
        R
          <
        h3TerminalForcingSecondQRadialProductNormAt
          hH3 hClass (hτ n) (p n).1 (p n).2 := by
      exact
        lt_of_mul_lt_mul_left
          hScaled
          (le_of_lt hCPos)

    exact
      hMLe.trans
        (le_of_lt hRLt)

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ p0 : Fin 3 × Fin 3,
          p n = p0 :=
    Frequently.of_forall
      (fun n => ⟨p n, rfl⟩)

  obtain ⟨p0, hFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySome

  obtain ⟨s, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop
      hFrequently

  have hs :
      ∀ n : ℕ, n ≤ s n := by
    intro n
    exact hMono.le_apply

  have hsTop :
      Tendsto s atTop atTop :=
    hMono.tendsto_atTop

  have hTopBeforeRewrite :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingSecondQRadialProductNormAt
            hH3 hClass (hτ (s n))
            (p (s n)).1
            (p (s n)).2)
        atTop atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingSecondQRadialProductNormAt
            hH3 hClass (hτ (s n))
            p0.1 p0.2)
        atTop atTop := by
    simpa only [hFixed] using hTopBeforeRewrite

  exact
    ⟨
      p0.1,
      p0.2,
      s,
      hs,
      hsTop,
      hTauTendsto.comp hsTop,
      hTop
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
