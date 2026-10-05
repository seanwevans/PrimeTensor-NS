import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Freeze a factor inside the third-q terminal state-mass group

The previous checkpoint freezes one of two Young groups:

* the product of two raw Fourier `L²` norms;
* the order-fourteen moment / raw-`L¹` Young mixture.

This file resolves each frozen group one level further.

For the raw-`L²` branch, product escape forces the maximum of its two factors
to escape, and finite extraction freezes one of them.

For the moment/`L¹` branch, the harmless split coefficient is strictly
positive.  Escape of the coefficient times the sum of two nonnegative Young
products therefore forces the maximum of those two products to escape, and
finite extraction freezes one product.

No analytic estimate is added; this is a finite algebraic decomposition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalThirdQForcingStateMassFactor
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalThirdQForcingStateMassFactor :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic two-channel extraction helpers -/

private theorem max_tendstoAtTop_of_mul_tendstoAtTop
    (A B : ℕ → ℝ)
    (hA : ∀ n : ℕ, 0 ≤ A n)
    (hB : ∀ n : ℕ, 0 ≤ B n)
    (hProduct :
      Tendsto
        (fun n : ℕ => A n * B n)
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ => max (A n) (B n))
      atTop
      atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ :=
    max M 0

  have hR0 :
      0 ≤ R := by
    dsimp only [R]
    exact le_max_right M 0

  have hMLe :
      M ≤ R := by
    dsimp only [R]
    exact le_max_left M 0

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        R ^ 2 < A n * B n :=
    hProduct.eventually
      (eventually_gt_atTop (R ^ 2))

  filter_upwards [hLarge] with n hn

  let H : ℝ :=
    max (A n) (B n)

  have hAH :
      A n ≤ H := by
    dsimp only [H]
    exact le_max_left _ _

  have hBH :
      B n ≤ H := by
    dsimp only [H]
    exact le_max_right _ _

  have hH0 :
      0 ≤ H :=
    (hA n).trans hAH

  have hProductLe :
      A n * B n ≤ H ^ 2 := by
    have hFirst :
        A n * B n ≤ H * B n :=
      mul_le_mul_of_nonneg_right
        hAH
        (hB n)

    have hSecond :
        H * B n ≤ H * H :=
      mul_le_mul_of_nonneg_left
        hBH
        hH0

    calc
      A n * B n ≤ H * B n := hFirst
      _ ≤ H * H := hSecond
      _ = H ^ 2 := by ring

  have hRSqLt :
      R ^ 2 < H ^ 2 :=
    lt_of_lt_of_le
      hn
      hProductLe

  have hRLt :
      R < H := by
    nlinarith

  change M ≤ max (A n) (B n)

  exact
    hMLe.trans
      (le_of_lt hRLt)

private theorem max_tendstoAtTop_of_posConst_mul_add_tendstoAtTop
    (C : ℝ)
    (A B : ℕ → ℝ)
    (hC : 0 < C)
    (hSum :
      Tendsto
        (fun n : ℕ => C * (A n + B n))
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ => max (A n) (B n))
      atTop
      atTop := by

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
        C * (2 * R)
          <
        C * (A n + B n) :=
    hSum.eventually
      (eventually_gt_atTop (C * (2 * R)))

  filter_upwards [hLarge] with n hn

  let H : ℝ :=
    max (A n) (B n)

  have hAH :
      A n ≤ H := by
    dsimp only [H]
    exact le_max_left _ _

  have hBH :
      B n ≤ H := by
    dsimp only [H]
    exact le_max_right _ _

  have hSumLe :
      A n + B n ≤ 2 * H := by
    linarith

  have hRLt :
      R < H := by

    by_contra hNot

    have hHLe :
        H ≤ R :=
      le_of_not_gt hNot

    have hTwoHLe :
        2 * H ≤ 2 * R := by
      linarith

    have hABLe :
        A n + B n ≤ 2 * R :=
      hSumLe.trans hTwoHLe

    have hScaled :
        C * (A n + B n)
          ≤
        C * (2 * R) :=
      mul_le_mul_of_nonneg_left
        hABLe
        hC.le

    exact
      (not_lt_of_ge hScaled)
        hn

  change M ≤ max (A n) (B n)

  exact
    hMLe.trans
      (le_of_lt hRLt)

private theorem exists_fixed_fin2_subsequence_of_max_tendstoAtTop
    (F : Fin 2 → ℕ → ℝ)
    (hMax :
      Tendsto
        (fun n : ℕ => max (F 0 n) (F 1 n))
        atTop
        atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => F q (s n))
          atTop
          atTop := by

  classical

  let q : ℕ → Fin 2 :=
    fun n =>
      if F 1 n ≤ F 0 n then
        0
      else
        1

  have hChosen :
      ∀ n : ℕ,
        F (q n) n
          =
        max (F 0 n) (F 1 n) := by

    intro n

    dsimp only [q]

    by_cases h :
        F 1 n ≤ F 0 n

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
        (fun n : ℕ => F (q n) n)
        atTop
        atTop := by
    simpa only [hChosen] using
      hMax

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q0 : Fin 2,
          q n = q0 :=
    Frequently.of_forall
      (
        fun n =>
          ⟨
            q n,
            rfl
          ⟩
      )

  obtain
    ⟨q0, hFrequently⟩ :=
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

  have hTopBeforeRewrite :
      Tendsto
        (fun n : ℕ => F (q (s n)) (s n))
        atTop
        atTop :=
    hChosenTop.comp
      hsTop

  have hTop :
      Tendsto
        (fun n : ℕ => F q0 (s n))
        atTop
        atTop := by
    simpa only [hFixed] using
      hTopBeforeRewrite

  exact
    ⟨
      q0,
      s,
      hs,
      hsTop,
      hTop
    ⟩

/-! ## Raw-L² product branch -/

/--
The two primitive raw-Fourier `L²` factors of the frozen Young pair.
Channel `0` is the conjugated raw `L²` norm of component `k`; channel `1` is
the raw `L²` norm of component `l`.
-/
noncomputable def h3TerminalForcingThirdQRawL2FactorAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 2) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  if q = 0 then
    ‖h3SpectralScalarRawFourierConjL2 (U k)‖
  else
    ‖h3SpectralScalarRawFourierL2 (U l)‖

theorem h3TerminalForcingThirdQRawL2FactorAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 2) :
    0 ≤
      h3TerminalForcingThirdQRawL2FactorAt
        hH3 hClass ht k l q := by

  unfold h3TerminalForcingThirdQRawL2FactorAt
  dsimp only

  split_ifs <;>
    exact norm_nonneg _

theorem h3TerminalForcingThirdQRawL2ProductAt_eq_factors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingThirdQRawL2ProductAt
        hH3 hClass ht k l
      =
    h3TerminalForcingThirdQRawL2FactorAt
        hH3 hClass ht k l 0
      *
    h3TerminalForcingThirdQRawL2FactorAt
        hH3 hClass ht k l 1 := by

  unfold h3TerminalForcingThirdQRawL2ProductAt
  unfold h3TerminalForcingThirdQRawL2FactorAt
  dsimp only
  norm_num

/--
Escape of the frozen raw-`L²` product admits a cofinal subsequence on which one
fixed raw-`L²` factor diverges.
-/
theorem exists_fixed_h3TerminalForcingThirdQRawL2Factor_subsequence_of_product_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hProductTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQRawL2ProductAt
              hH3 hClass (hτ n) k l
        )
        atTop
        atTop) :
    ∃ q : Fin 2,
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
              h3TerminalForcingThirdQRawL2FactorAt
                hH3 hClass (hτ (s n)) k l q
          )
          atTop
          atTop := by

  have hFactorProductTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQRawL2FactorAt
                hH3 hClass (hτ n) k l 0
              *
            h3TerminalForcingThirdQRawL2FactorAt
              hH3 hClass (hτ n) k l 1
        )
        atTop
        atTop := by
    simpa only [
      ← h3TerminalForcingThirdQRawL2ProductAt_eq_factors
    ] using hProductTop

  have hMaxTop :
      Tendsto
        (
          fun n : ℕ =>
            max
              (
                h3TerminalForcingThirdQRawL2FactorAt
                  hH3 hClass (hτ n) k l 0
              )
              (
                h3TerminalForcingThirdQRawL2FactorAt
                  hH3 hClass (hτ n) k l 1
              )
        )
        atTop
        atTop :=
    max_tendstoAtTop_of_mul_tendstoAtTop
      (
        fun n : ℕ =>
          h3TerminalForcingThirdQRawL2FactorAt
            hH3 hClass (hτ n) k l 0
      )
      (
        fun n : ℕ =>
          h3TerminalForcingThirdQRawL2FactorAt
            hH3 hClass (hτ n) k l 1
      )
      (
        fun n =>
          h3TerminalForcingThirdQRawL2FactorAt_nonneg
            hH3 hClass (hτ n) k l 0
      )
      (
        fun n =>
          h3TerminalForcingThirdQRawL2FactorAt_nonneg
            hH3 hClass (hτ n) k l 1
      )
      hFactorProductTop

  obtain
    ⟨q, s, hs, hsTop, hFactorTop⟩ :=
    exists_fixed_fin2_subsequence_of_max_tendstoAtTop
      (
        fun q n =>
          h3TerminalForcingThirdQRawL2FactorAt
            hH3 hClass (hτ n) k l q
      )
      hMaxTop

  exact
    ⟨
      q,
      s,
      hs,
      hsTop,
      hTauTendsto.comp hsTop,
      hFactorTop
    ⟩

/-! ## Moment / L¹ mixture branch -/

/--
The two nonnegative Young products inside the order-fourteen moment / raw-`L¹`
mixture. Channel `0` is `M14(k) * L1(l)` and channel `1` is
`L1(k) * M14(l)`.
-/
noncomputable def h3TerminalForcingThirdQMomentL1ProductAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 2) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  if q = 0 then
    h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U k)
      *
    h3SpectralScalarRawFourierL1Mass (U l)
  else
    h3SpectralScalarRawFourierL1Mass (U k)
      *
    h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U l)

theorem h3TerminalForcingThirdQMomentL1ProductAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 2) :
    0 ≤
      h3TerminalForcingThirdQMomentL1ProductAt
        hH3 hClass ht k l q := by

  unfold h3TerminalForcingThirdQMomentL1ProductAt
  dsimp only

  split_ifs

  · exact
      mul_nonneg
        (h3SpectralScalarRawFourierMomentMass_nonneg
          (14 : ℝ) _)
        (h3SpectralScalarRawFourierL1Mass_nonneg _)

  · exact
      mul_nonneg
        (h3SpectralScalarRawFourierL1Mass_nonneg _)
        (h3SpectralScalarRawFourierMomentMass_nonneg
          (14 : ℝ) _)

theorem h3FourierMomentSplitCoefficient_fourteen_pos :
    0 < h3FourierMomentSplitCoefficient (14 : ℝ) := by

  unfold h3FourierMomentSplitCoefficient

  exact
    Real.rpow_pos_of_pos
      (by norm_num)
      (14 : ℝ)

theorem h3TerminalForcingThirdQMomentL1MixAt_eq_products
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingThirdQMomentL1MixAt
        hH3 hClass ht k l
      =
    h3FourierMomentSplitCoefficient (14 : ℝ)
      *
    (
      h3TerminalForcingThirdQMomentL1ProductAt
          hH3 hClass ht k l 0
        +
      h3TerminalForcingThirdQMomentL1ProductAt
        hH3 hClass ht k l 1
    ) := by

  unfold h3TerminalForcingThirdQMomentL1MixAt
  unfold h3TerminalForcingThirdQMomentL1ProductAt
  dsimp only
  norm_num

/--
Escape of the frozen moment/`L¹` mixture admits a cofinal subsequence on which
one fixed Young product diverges.
-/
theorem exists_fixed_h3TerminalForcingThirdQMomentL1Product_subsequence_of_mix_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hMixTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMomentL1MixAt
              hH3 hClass (hτ n) k l
        )
        atTop
        atTop) :
    ∃ q : Fin 2,
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
              h3TerminalForcingThirdQMomentL1ProductAt
                hH3 hClass (hτ (s n)) k l q
          )
          atTop
          atTop := by

  have hSumTop :
      Tendsto
        (
          fun n : ℕ =>
            h3FourierMomentSplitCoefficient (14 : ℝ)
              *
            (
              h3TerminalForcingThirdQMomentL1ProductAt
                  hH3 hClass (hτ n) k l 0
                +
              h3TerminalForcingThirdQMomentL1ProductAt
                hH3 hClass (hτ n) k l 1
            )
        )
        atTop
        atTop := by
    simpa only [
      ← h3TerminalForcingThirdQMomentL1MixAt_eq_products
    ] using hMixTop

  have hMaxTop :
      Tendsto
        (
          fun n : ℕ =>
            max
              (
                h3TerminalForcingThirdQMomentL1ProductAt
                  hH3 hClass (hτ n) k l 0
              )
              (
                h3TerminalForcingThirdQMomentL1ProductAt
                  hH3 hClass (hτ n) k l 1
              )
        )
        atTop
        atTop :=
    max_tendstoAtTop_of_posConst_mul_add_tendstoAtTop
      (h3FourierMomentSplitCoefficient (14 : ℝ))
      (
        fun n : ℕ =>
          h3TerminalForcingThirdQMomentL1ProductAt
            hH3 hClass (hτ n) k l 0
      )
      (
        fun n : ℕ =>
          h3TerminalForcingThirdQMomentL1ProductAt
            hH3 hClass (hτ n) k l 1
      )
      h3FourierMomentSplitCoefficient_fourteen_pos
      hSumTop

  obtain
    ⟨q, s, hs, hsTop, hProductTop⟩ :=
    exists_fixed_fin2_subsequence_of_max_tendstoAtTop
      (
        fun q n =>
          h3TerminalForcingThirdQMomentL1ProductAt
            hH3 hClass (hτ n) k l q
      )
      hMaxTop

  exact
    ⟨
      q,
      s,
      hs,
      hsTop,
      hTauTendsto.comp hsTop,
      hProductTop
    ⟩

/-! ## Resolve the frozen group -/

/--
A fixed state-mass group escape resolves into either one fixed raw-`L²` factor
or one fixed order-fourteen-moment/raw-`L¹` product on a cofinal subsequence.
-/
theorem h3TerminalForcingThirdQStateMassGroup_escape_resolves_factor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k l : Fin 3)
    (q : Fin 2)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hGroupTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQStateMassGroupAt
              hH3 hClass (hτ n) k l q
        )
        atTop
        atTop) :
    (
      ∃ r : Fin 2,
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
                h3TerminalForcingThirdQRawL2FactorAt
                  hH3 hClass (hτ (s n)) k l r
            )
            atTop
            atTop
    )
      ∨
    (
      ∃ r : Fin 2,
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
                h3TerminalForcingThirdQMomentL1ProductAt
                  hH3 hClass (hτ (s n)) k l r
            )
            atTop
            atTop
    ) := by

  fin_cases q

  · have hRawTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQRawL2ProductAt
                hH3 hClass (hτ n) k l
          )
          atTop
          atTop := by
      simpa [
        h3TerminalForcingThirdQStateMassGroupAt
      ] using hGroupTop

    exact
      Or.inl
        (
          exists_fixed_h3TerminalForcingThirdQRawL2Factor_subsequence_of_product_tendstoAtTop
            hH3 hClass k l τ hτ hTauTendsto hRawTop
        )

  · have hMixTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQMomentL1MixAt
                hH3 hClass (hτ n) k l
          )
          atTop
          atTop := by
      simpa [
        h3TerminalForcingThirdQStateMassGroupAt
      ] using hGroupTop

    exact
      Or.inr
        (
          exists_fixed_h3TerminalForcingThirdQMomentL1Product_subsequence_of_mix_tendstoAtTop
            hH3 hClass k l τ hτ hTauTendsto hMixTop
        )

/--
The sixth-diffusion frontier now reduces to the old shift-four higher-radial
velocity branch, or to a fixed primitive raw-`L²` factor, or to a fixed
order-fourteen-moment/raw-`L¹` Young product.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingStateMassFactor
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
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass 4
                (τ (s n))
                (hτ (s n))
          )
          atTop
          (𝓝 ∞)
    )
      ∨
    (
      ∃ k l : Fin 3,
        (
          (
            ∃ r : Fin 2,
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
                      h3TerminalForcingThirdQRawL2FactorAt
                        hH3 hClass (hτ (s n)) k l r
                  )
                  atTop
                  atTop
          )
            ∨
          (
            ∃ r : Fin 2,
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
                      h3TerminalForcingThirdQMomentL1ProductAt
                        hH3 hClass (hτ (s n)) k l r
                  )
                  atTop
                  atTop
          )
        )
    ) := by

  rcases
    sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingStateMassGroup
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    hHigher
    |
    hGroup

  · exact
      Or.inl hHigher

  · rcases hGroup with
      ⟨k, l, q, s, hs, hsTop, hTauSub, hGroupTop⟩

    rcases
      h3TerminalForcingThirdQStateMassGroup_escape_resolves_factor
        hH3 hClass k l q
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hTauSub
        hGroupTop
    with
      hRaw
      |
      hMomentL1

    · rcases hRaw with
        ⟨r, v, hv, hvTop, hTauFinal, hFactorTop⟩

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
            atTop
            atTop :=
        hsTop.comp hvTop

      exact
        Or.inr
          ⟨
            k,
            l,
            Or.inl
              ⟨
                r,
                (fun n : ℕ => s (v n)),
                hComp,
                hCompTop,
                hTauFinal,
                hFactorTop
              ⟩
          ⟩

    · rcases hMomentL1 with
        ⟨r, v, hv, hvTop, hTauFinal, hProductTop⟩

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
            atTop
            atTop :=
        hsTop.comp hvTop

      exact
        Or.inr
          ⟨
            k,
            l,
            Or.inr
              ⟨
                r,
                (fun n : ℕ => s (v n)),
                hComp,
                hCompTop,
                hTauFinal,
                hProductTop
              ⟩
          ⟩

end

end Euclidean
end Bridge
end PrimeTensor
