import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Subtail.StateMass.Group.Factor.Primitive.Origin.Higher.ProjectedRHSMoment10StateEnvelope
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Close the projected-RHS order-ten moment obstruction

The sole residual fourth-q projected-RHS primitive has already been bounded by
a finite quadratic polynomial in the three coordinate envelopes

    E_k = L¹(U_k) + M₁₄(U_k).

This file performs only finite-channel asymptotics:

1. escape of the projected-RHS `M₁₀` forces escape of
   `max E_0 (max E_1 E_2)`;
2. a cofinal subsequence freezes one coordinate `k`;
3. escape of `E_k` freezes either raw `L¹(U_k)` or `M₁₄(U_k)`;
4. raw `L¹` gives physical H³-energy escape;
5. `M₁₄` is the already-closed higher-radial branch.

Thus the projected-RHS residual disappears entirely from the fourth-temporal
frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 3000000

noncomputable local instance axisFintypeH3TerminalFourthQProjectedRHSMomentTenClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQProjectedRHSMomentTenClosure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic finite extraction helpers -/

private theorem exists_fixed_fin3_subsequence_of_nestedMax_tendstoAtTop
    (F : Fin 3 → ℕ → ℝ)
    (hMax :
      Tendsto
        (fun n : ℕ =>
          max
            (F 0 n)
            (max (F 1 n) (F 2 n)))
        atTop atTop) :
    ∃ k : Fin 3,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => F k (s n))
          atTop atTop := by

  classical

  have hChoice :
      ∀ n : ℕ,
        ∃ k : Fin 3,
          F k n =
            max
              (F 0 n)
              (max (F 1 n) (F 2 n)) := by

    intro n

    by_cases h10 : F 1 n ≤ F 0 n

    · by_cases h20 : F 2 n ≤ F 0 n

      · refine ⟨0, ?_⟩

        have hInner :
            max (F 1 n) (F 2 n) ≤ F 0 n :=
          max_le h10 h20

        exact
          (max_eq_left hInner).symm

      · refine ⟨2, ?_⟩

        have h02 :
            F 0 n ≤ F 2 n :=
          le_of_lt (lt_of_not_ge h20)

        have h12 :
            F 1 n ≤ F 2 n :=
          h10.trans h02

        rw [max_eq_right h12]
        exact
          (max_eq_right h02).symm

    · have h01 :
          F 0 n ≤ F 1 n :=
        le_of_lt (lt_of_not_ge h10)

      by_cases h21 : F 2 n ≤ F 1 n

      · refine ⟨1, ?_⟩

        rw [max_eq_left h21]
        exact
          (max_eq_right h01).symm

      · refine ⟨2, ?_⟩

        have h12 :
            F 1 n ≤ F 2 n :=
          le_of_lt (lt_of_not_ge h21)

        have h02 :
            F 0 n ≤ F 2 n :=
          h01.trans h12

        rw [max_eq_right h12]
        exact
          (max_eq_right h02).symm

  choose k hk using hChoice

  have hChosenTop :
      Tendsto
        (fun n : ℕ => F (k n) n)
        atTop atTop := by
    simpa only [hk] using hMax

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ k0 : Fin 3,
          k n = k0 :=
    Frequently.of_forall
      (fun n => ⟨k n, rfl⟩)

  obtain
    ⟨k0, hFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySome

  obtain
    ⟨s, hMono, hFixed⟩ :=
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
          F (k (s n)) (s n))
        atTop atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ =>
          F k0 (s n))
        atTop atTop := by
    simpa only [hFixed] using hTopBeforeRewrite

  exact
    ⟨k0, s, hs, hsTop, hTop⟩

private theorem exists_fixed_fin2_subsequence_of_max_tendstoAtTop
    (F : Fin 2 → ℕ → ℝ)
    (hMax :
      Tendsto
        (fun n : ℕ =>
          max (F 0 n) (F 1 n))
        atTop atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => F q (s n))
          atTop atTop := by

  classical

  let q : ℕ → Fin 2 :=
    fun n =>
      if F 1 n ≤ F 0 n then 0 else 1

  have hChosen :
      ∀ n : ℕ,
        F (q n) n =
          max (F 0 n) (F 1 n) := by

    intro n
    dsimp only [q]

    by_cases h : F 1 n ≤ F 0 n

    · simp only [if_pos h]
      exact
        (max_eq_left h).symm

    · simp only [if_neg h]

      have hReverse :
          F 0 n ≤ F 1 n :=
        le_of_lt
          (lt_of_not_ge h)

      exact
        (max_eq_right hReverse).symm

  have hChosenTop :
      Tendsto
        (fun n : ℕ =>
          F (q n) n)
        atTop atTop := by
    simpa only [hChosen] using hMax

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q0 : Fin 2,
          q n = q0 :=
    Frequently.of_forall
      (fun n => ⟨q n, rfl⟩)

  obtain
    ⟨q0, hFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySome

  obtain
    ⟨s, hMono, hFixed⟩ :=
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
          F (q (s n)) (s n))
        atTop atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ =>
          F q0 (s n))
        atTop atTop := by
    simpa only [hFixed] using hTopBeforeRewrite

  exact
    ⟨q0, s, hs, hsTop, hTop⟩

/-! ## Projected-RHS escape forces one terminal coordinate envelope -/

theorem h3TerminalFourthQProjectedRHSMoment10StateEnvelopeMax_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        max
          (h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
            hH3 hClass (hτ n) 0)
          (max
            (h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass (hτ n) 1)
            (h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass (hτ n) 2)))
      atTop atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ :=
    max M 0

  let C : ℝ :=
    (2 * Real.pi) ^ 2

  let D : ℝ :=
    (2 * Real.pi) *
      h3FourierMomentSplitCoefficient (11 : ℝ)

  have hR0 :
      0 ≤ R := by
    dsimp only [R]
    exact le_max_right M 0

  have hMLe :
      M ≤ R := by
    dsimp only [R]
    exact le_max_left M 0

  have hC0 :
      0 ≤ C := by
    dsimp only [C]
    positivity

  have hD0 :
      0 ≤ D := by
    dsimp only [D]
    apply mul_nonneg
    · positivity
    · exact
        h3FourierMomentSplitCoefficient_nonneg (11 : ℝ)

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        C * R + 36 * D * R ^ 2 + 1
          <
        h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
          hH3 hClass (hτ n) j i :=
    hMomentTop.eventually
      (eventually_gt_atTop
        (C * R + 36 * D * R ^ 2 + 1))

  filter_upwards [hLarge] with n hn

  let E : Fin 3 → ℝ :=
    fun k =>
      h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
        hH3 hClass (hτ n) k

  let H : ℝ :=
    max
      (E 0)
      (max (E 1) (E 2))

  have hE0 :
      ∀ k : Fin 3,
        0 ≤ E k := by

    intro k

    dsimp only [E]

    exact
      h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt_nonneg
        hH3 hClass (hτ n) k

  have hEH :
      ∀ k : Fin 3,
        E k ≤ H := by

    intro k
    fin_cases k

    · dsimp only [H]
      exact
        le_max_left _ _

    · dsimp only [H]

      exact
        (le_max_left (E 1) (E 2)).trans
          (le_max_right (E 0) (max (E 1) (E 2)))

    · dsimp only [H]

      exact
        (le_max_right (E 1) (E 2)).trans
          (le_max_right (E 0) (max (E 1) (E 2)))

  have hH0 :
      0 ≤ H :=
    (hE0 0).trans
      (hEH 0)

  have hPair :
      ∀ k l : Fin 3,
        E k * E l + E k * E l
          ≤
        2 * H ^ 2 := by

    intro k l

    have hProd :
        E k * E l ≤ H * H :=
      mul_le_mul
        (hEH k)
        (hEH l)
        (hE0 l)
        hH0

    nlinarith

  have hEach :
      ∀ k l : Fin 3,
        (2 * Real.pi) *
            (
              h3FourierMomentSplitCoefficient (11 : ℝ) *
                (E k * E l + E k * E l)
            )
          ≤
        D * (2 * H ^ 2) := by

    intro k l

    have hScaled :
        h3FourierMomentSplitCoefficient (11 : ℝ) *
            (E k * E l + E k * E l)
          ≤
        h3FourierMomentSplitCoefficient (11 : ℝ) *
            (2 * H ^ 2) :=
      mul_le_mul_of_nonneg_left
        (hPair k l)
        (h3FourierMomentSplitCoefficient_nonneg (11 : ℝ))

    calc
      (2 * Real.pi) *
          (
            h3FourierMomentSplitCoefficient (11 : ℝ) *
              (E k * E l + E k * E l)
          )
          ≤
        (2 * Real.pi) *
          (
            h3FourierMomentSplitCoefficient (11 : ℝ) *
              (2 * H ^ 2)
          ) :=
        mul_le_mul_of_nonneg_left
          hScaled
          (by positivity)
      _ =
        D * (2 * H ^ 2) := by
        dsimp only [D]
        ring

  have hSum :
      (∑ k : Fin 3,
        ∑ l : Fin 3,
          (2 * Real.pi) *
            (
              h3FourierMomentSplitCoefficient (11 : ℝ) *
                (E k * E l + E k * E l)
            ))
        ≤
      18 * D * H ^ 2 := by

    calc
      (∑ k : Fin 3,
        ∑ l : Fin 3,
          (2 * Real.pi) *
            (
              h3FourierMomentSplitCoefficient (11 : ℝ) *
                (E k * E l + E k * E l)
            ))
          ≤
        ∑ k : Fin 3,
          ∑ l : Fin 3,
            D * (2 * H ^ 2) := by

            apply Finset.sum_le_sum
            intro k hk

            apply Finset.sum_le_sum
            intro l hl

            exact hEach k l

      _ =
        18 * D * H ^ 2 := by
        simp only [Fin.sum_univ_three]
        ring

  have hNonlinear :
      2 *
          (∑ k : Fin 3,
            ∑ l : Fin 3,
              (2 * Real.pi) *
                (
                  h3FourierMomentSplitCoefficient (11 : ℝ) *
                    (E k * E l + E k * E l)
                ))
        ≤
      36 * D * H ^ 2 := by

    calc
      2 *
          (∑ k : Fin 3,
            ∑ l : Fin 3,
              (2 * Real.pi) *
                (
                  h3FourierMomentSplitCoefficient (11 : ℝ) *
                    (E k * E l + E k * E l)
                ))
          ≤
        2 * (18 * D * H ^ 2) :=
        mul_le_mul_of_nonneg_left
          hSum
          (by norm_num)
      _ =
        36 * D * H ^ 2 := by
        ring

  have hBound :=
    h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt_le_stateEnvelopePolynomial
      hH3 hClass (hτ n) j i

  have hDiffusion :
      C * E i
        ≤
      C * H :=
    mul_le_mul_of_nonneg_left
      (hEH i)
      hC0

  have hMassLe :
      h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
          hH3 hClass (hτ n) j i
        ≤
      C * H + 36 * D * H ^ 2 := by

    dsimp only [E, C, D] at hBound ⊢

    exact
      hBound.trans
        (add_le_add
          hDiffusion
          hNonlinear)

  have hRLtH :
      R < H := by

    by_contra hNot

    have hHLe :
        H ≤ R :=
      le_of_not_gt hNot

    have hSq :
        H ^ 2 ≤ R ^ 2 := by
      nlinarith

    have hLinear :
        C * H ≤ C * R :=
      mul_le_mul_of_nonneg_left
        hHLe
        hC0

    have hQuad :
        36 * D * H ^ 2
          ≤
        36 * D * R ^ 2 := by

      have hCoeff0 :
          0 ≤ 36 * D := by
        positivity

      exact
        mul_le_mul_of_nonneg_left
          hSq
          hCoeff0

    have hPoly :
        C * H + 36 * D * H ^ 2
          ≤
        C * R + 36 * D * R ^ 2 :=
      add_le_add hLinear hQuad

    have hFinal :
        h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
            hH3 hClass (hτ n) j i
          ≤
        C * R + 36 * D * R ^ 2 :=
      hMassLe.trans hPoly

    linarith

  change
    M ≤
      max
        (h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
          hH3 hClass (hτ n) 0)
        (max
          (h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
            hH3 hClass (hτ n) 1)
          (h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
            hH3 hClass (hτ n) 2))

  exact
    hMLe.trans
      (le_of_lt hRLtH)

theorem exists_fixed_h3TerminalFourthQProjectedRHSMoment10StateEnvelope_subsequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    ∃ k : Fin 3,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass (hτ (s n)) k)
          atTop atTop := by

  have hMax :=
    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeMax_tendstoAtTop
      hH3 hClass j i τ hτ hMomentTop

  obtain
    ⟨k, s, hs, hsTop, hEnvelopeTop⟩ :=
    exists_fixed_fin3_subsequence_of_nestedMax_tendstoAtTop
      (fun k n =>
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
          hH3 hClass (hτ n) k)
      hMax

  exact
    ⟨
      k,
      s,
      hs,
      hsTop,
      hTauTendsto.comp hsTop,
      hEnvelopeTop
    ⟩

/-! ## Freeze raw L¹ versus order-fourteen inside one state envelope -/

noncomputable def h3TerminalFourthQProjectedRHSMoment10StateEnvelopeResolverAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k : Fin 3)
    (q : Fin 2) : ℝ :=
  if q = 0 then
    h3TerminalForcingThirdQRawL1MassAt
      hH3 hClass ht k
  else
    h3TerminalForcingThirdQMoment14MassAt
      hH3 hClass ht k

theorem h3TerminalFourthQProjectedRHSMoment10StateEnvelopeResolverMax_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hEnvelopeTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
            hH3 hClass (hτ n) k)
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        max
          (h3TerminalForcingThirdQRawL1MassAt
            hH3 hClass (hτ n) k)
          (h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) k))
      atTop atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ :=
    max M 0

  have hMLe :
      M ≤ R := by
    dsimp only [R]
    exact le_max_left M 0

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        2 * R + 1
          <
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
          hH3 hClass (hτ n) k :=
    hEnvelopeTop.eventually
      (eventually_gt_atTop (2 * R + 1))

  filter_upwards [hLarge] with n hn

  let A : ℝ :=
    h3TerminalForcingThirdQRawL1MassAt
      hH3 hClass (hτ n) k

  let B : ℝ :=
    h3TerminalForcingThirdQMoment14MassAt
      hH3 hClass (hτ n) k

  let H : ℝ :=
    max A B

  have hAH :
      A ≤ H := by
    dsimp only [H]
    exact le_max_left A B

  have hBH :
      B ≤ H := by
    dsimp only [H]
    exact le_max_right A B

  have hRLtH :
      R < H := by

    by_contra hNot

    have hHLe :
        H ≤ R :=
      le_of_not_gt hNot

    have hALe :
        A ≤ R :=
      hAH.trans hHLe

    have hBLe :
        B ≤ R :=
      hBH.trans hHLe

    have hSum :
        A + B ≤ 2 * R := by
      linarith

    have hEnvelopeLe :
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
            hH3 hClass (hτ n) k
          ≤
        2 * R := by

      unfold h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt

      dsimp only [A, B] at hSum ⊢

      exact hSum

    linarith

  change
    M ≤
      max
        (h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass (hτ n) k)
        (h3TerminalForcingThirdQMoment14MassAt
          hH3 hClass (hτ n) k)

  exact
    hMLe.trans
      (le_of_lt hRLtH)

theorem exists_fixed_h3TerminalFourthQProjectedRHSMoment10StateEnvelopeResolver_subsequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hEnvelopeTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
            hH3 hClass (hτ n) k)
        atTop atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalFourthQProjectedRHSMoment10StateEnvelopeResolverAt
              hH3 hClass (hτ (s n)) k q)
          atTop atTop := by

  have hMax :=
    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeResolverMax_tendstoAtTop
      hH3 hClass k τ hτ hEnvelopeTop

  obtain
    ⟨q, s, hs, hsTop, hResolverTop⟩ :=
    exists_fixed_fin2_subsequence_of_max_tendstoAtTop
      (fun q n =>
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeResolverAt
          hH3 hClass (hτ n) k q)
      (by
        simpa [
          h3TerminalFourthQProjectedRHSMoment10StateEnvelopeResolverAt
        ] using hMax)

  exact
    ⟨
      q,
      s,
      hs,
      hsTop,
      hTauTendsto.comp hsTop,
      hResolverTop
    ⟩

/-! ## Close projected-RHS M10 -/

/--
Escape of the sole projected-RHS order-ten primitive is not a new obstruction:
after cofinal extraction it is absorbed by physical H³ energy or one already
existing nonzero extended higher-radial moment.
-/
theorem h3TerminalFourthQProjectedRHSMoment10_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            velocityH3EnergyAt u (τ (s n)))
          atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto
            (fun n : ℕ => τ (s n))
            atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop (𝓝 ∞)
    ) := by

  obtain
    ⟨k, s, hs, hsTop, hTauSub, hEnvelopeTop⟩ :=
    exists_fixed_h3TerminalFourthQProjectedRHSMoment10StateEnvelope_subsequence
      hH3 hClass j i τ hτ hTauTendsto hMomentTop

  obtain
    ⟨q, v, hv, hvTop, hTauResolver, hResolverTop⟩ :=
    exists_fixed_h3TerminalFourthQProjectedRHSMoment10StateEnvelopeResolver_subsequence
      hH3 hClass k
      (fun n : ℕ => τ (s n))
      (fun n : ℕ => hτ (s n))
      hTauSub
      hEnvelopeTop

  have hComp :
      ∀ n : ℕ, n ≤ s (v n) := by
    intro n
    exact
      le_trans
        (hv n)
        (hs (v n))

  have hCompTop :
      Tendsto
        (fun n : ℕ => s (v n))
        atTop atTop :=
    hsTop.comp hvTop

  fin_cases q

  · have hL1Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass
              (hτ (s (v n)))
              k)
          atTop atTop := by

      simpa [
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeResolverAt
      ] using hResolverTop

    have hEnergyTop :=
      velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
        hH3 hClass k
        (fun n : ℕ => τ (s (v n)))
        (fun n : ℕ => hτ (s (v n)))
        hL1Top

    exact
      Or.inl
        ⟨
          (fun n : ℕ => s (v n)),
          hComp,
          hCompTop,
          hTauResolver,
          hEnergyTop
        ⟩

  · have hMoment14Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingThirdQMoment14MassAt
              hH3 hClass
              (hτ (s (v n)))
              k)
          atTop atTop := by

      simpa [
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeResolverAt
      ] using hResolverTop

    obtain
      ⟨qRadial, w, hw, hwTop, hTauFinal, hSquareTop⟩ :=
      exists_fixed_h3TerminalForcingThirdQMoment14RadialSquareChannel_subsequence
        hH3 hClass k
        (fun n : ℕ => τ (s (v n)))
        (fun n : ℕ => hτ (s (v n)))
        hTauResolver
        hMoment14Top

    have hHigherTop :=
      h3TerminalForcingThirdQMoment14RadialSquareChannel_escape_resolves_higherRadial
        hH3 hClass k qRadial
        (fun n : ℕ => τ (s (v (w n))))
        (fun n : ℕ => hτ (s (v (w n))))
        hSquareTop

    have hCompFinal :
        ∀ n : ℕ,
          n ≤ s (v (w n)) := by
      intro n
      exact
        le_trans
          (hw n)
          (
            le_trans
              (hv (w n))
              (hs (v (w n)))
          )

    have hCompFinalTop :
        Tendsto
          (fun n : ℕ => s (v (w n)))
          atTop atTop :=
      hsTop.comp
        (hvTop.comp hwTop)

    have hShiftNe :
        h3TerminalForcingThirdQHigherRadialShift qRadial ≠ 0 := by
      fin_cases qRadial <;>
        norm_num [h3TerminalForcingThirdQHigherRadialShift]

    exact
      Or.inr
        ⟨
          h3TerminalForcingThirdQHigherRadialShift qRadial,
          hShiftNe,
          (fun n : ℕ => s (v (w n))),
          hCompFinal,
          hCompFinalTop,
          hTauFinal,
          hHigherTop
        ⟩

/-! ## Remove the projected-RHS residual from the fourth-temporal frontier -/

/--
The fourth-temporal Hilbert derivative channel is now fully reduced to the two
already-existing physical alternatives: H³-energy escape or one fixed nonzero
extended higher-radial moment.  There is no remaining projected-RHS primitive.
-/
theorem fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hFourth :
      Tendsto
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
            (τ n))
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            velocityH3EnergyAt u (τ (s n)))
          atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto
            (fun n : ℕ => τ (s n))
            atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop (𝓝 ∞)
    ) := by

  rcases
    fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedProjectedRHSMoment10
      hH3 hClass j τ hτ hTauTendsto hFourth
  with hEnergy | hRest

  · exact
      Or.inl hEnergy

  · rcases hRest with hHigher | hRHS

    · exact
        Or.inr hHigher

    · rcases hRHS with
        ⟨i, s, hs, hsTop, hTauSub, hMomentTop⟩

      rcases
        h3TerminalFourthQProjectedRHSMoment10_escape_energy_or_fixedExtendedHigherRadial
          hH3 hClass j i
          (fun n : ℕ => τ (s n))
          (fun n : ℕ => hτ (s n))
          hTauSub
          hMomentTop
      with hEnergySub | hHigherSub

      · rcases hEnergySub with
          ⟨v, hv, hvTop, hTauFinal, hEnergyTop⟩

        have hComp :
            ∀ n : ℕ,
              n ≤ s (v n) := by
          intro n
          exact
            le_trans
              (hv n)
              (hs (v n))

        have hCompTop :
            Tendsto
              (fun n : ℕ => s (v n))
              atTop atTop :=
          hsTop.comp hvTop

        exact
          Or.inl
            ⟨
              (fun n : ℕ => s (v n)),
              hComp,
              hCompTop,
              hTauFinal,
              hEnergyTop
            ⟩

      · rcases hHigherSub with
          ⟨m, hm, v, hv, hvTop, hTauFinal, hHigherTop⟩

        have hComp :
            ∀ n : ℕ,
              n ≤ s (v n) := by
          intro n
          exact
            le_trans
              (hv n)
              (hs (v n))

        have hCompTop :
            Tendsto
              (fun n : ℕ => s (v n))
              atTop atTop :=
          hsTop.comp hvTop

        exact
          Or.inr
            ⟨
              m,
              hm,
              (fun n : ℕ => s (v n)),
              hComp,
              hCompTop,
              hTauFinal,
              hHigherTop
            ⟩

end

end Euclidean
end Bridge
end PrimeTensor
