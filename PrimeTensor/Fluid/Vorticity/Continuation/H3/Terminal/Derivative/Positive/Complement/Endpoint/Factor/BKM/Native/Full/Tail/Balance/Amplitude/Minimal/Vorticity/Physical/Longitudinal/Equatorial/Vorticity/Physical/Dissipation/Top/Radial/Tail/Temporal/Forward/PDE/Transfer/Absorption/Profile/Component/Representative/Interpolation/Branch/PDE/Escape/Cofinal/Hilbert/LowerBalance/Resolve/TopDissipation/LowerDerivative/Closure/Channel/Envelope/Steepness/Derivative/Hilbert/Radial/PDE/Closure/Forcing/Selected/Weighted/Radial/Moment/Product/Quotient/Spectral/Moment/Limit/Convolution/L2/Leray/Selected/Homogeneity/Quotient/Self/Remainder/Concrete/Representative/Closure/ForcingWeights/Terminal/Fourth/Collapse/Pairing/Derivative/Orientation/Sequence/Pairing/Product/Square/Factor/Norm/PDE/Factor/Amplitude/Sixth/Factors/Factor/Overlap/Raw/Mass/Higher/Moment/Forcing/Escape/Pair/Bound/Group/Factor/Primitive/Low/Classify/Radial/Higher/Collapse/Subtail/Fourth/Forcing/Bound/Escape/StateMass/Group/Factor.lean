import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.Fourth.Forcing.Bound.Escape.StateMass.Group
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Freeze a primitive factor inside the fourth-q derivative state-mass group

The preceding checkpoint freezes one of two Young groups for one fixed
product-rule orientation and coordinate pair:

* the product of two raw Fourier `L²` norms;
* the order-ten moment / raw-`L¹` Young mixture.

This file resolves either group one level further.  Raw-`L²` product escape
forces one of its two factors to escape.  Moment/raw-`L¹` mixture escape forces
one of its two Young products to escape.

No PDE estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalFourthQForcingDerivativeStateMassFactor
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingDerivativeStateMassFactor :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic finite two-channel helpers -/

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

  let R0 : ℝ := max M 0

  have hR0 : 0 ≤ R0 := by
    dsimp only [R0]
    exact le_max_right M 0

  have hMLe : M ≤ R0 := by
    dsimp only [R0]
    exact le_max_left M 0

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        R0 ^ 2 < A n * B n :=
    hProduct.eventually
      (eventually_gt_atTop (R0 ^ 2))

  filter_upwards [hLarge] with n hn

  let H : ℝ := max (A n) (B n)

  have hAH : A n ≤ H := by
    dsimp only [H]
    exact le_max_left _ _

  have hBH : B n ≤ H := by
    dsimp only [H]
    exact le_max_right _ _

  have hH0 : 0 ≤ H :=
    (hA n).trans hAH

  have hProductLe : A n * B n ≤ H ^ 2 := by
    have hFirst : A n * B n ≤ H * B n :=
      mul_le_mul_of_nonneg_right hAH (hB n)
    have hSecond : H * B n ≤ H * H :=
      mul_le_mul_of_nonneg_left hBH hH0
    calc
      A n * B n ≤ H * B n := hFirst
      _ ≤ H * H := hSecond
      _ = H ^ 2 := by ring

  have hRSqLt : R0 ^ 2 < H ^ 2 :=
    lt_of_lt_of_le hn hProductLe

  have hRLt : R0 < H := by
    nlinarith

  change M ≤ max (A n) (B n)

  exact hMLe.trans (le_of_lt hRLt)

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

  let R0 : ℝ := max M 0

  have hMLe : M ≤ R0 := by
    dsimp only [R0]
    exact le_max_left M 0

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        C * (2 * R0)
          <
        C * (A n + B n) :=
    hSum.eventually
      (eventually_gt_atTop (C * (2 * R0)))

  filter_upwards [hLarge] with n hn

  let H : ℝ := max (A n) (B n)

  have hAH : A n ≤ H := by
    dsimp only [H]
    exact le_max_left _ _

  have hBH : B n ≤ H := by
    dsimp only [H]
    exact le_max_right _ _

  have hSumLe : A n + B n ≤ 2 * H := by
    linarith

  have hRLt : R0 < H := by
    by_contra hNot

    have hHLe : H ≤ R0 :=
      le_of_not_gt hNot

    have hTwoHLe : 2 * H ≤ 2 * R0 := by
      linarith

    have hABLe : A n + B n ≤ 2 * R0 :=
      hSumLe.trans hTwoHLe

    have hScaled :
        C * (A n + B n) ≤ C * (2 * R0) :=
      mul_le_mul_of_nonneg_left hABLe hC.le

    exact (not_lt_of_ge hScaled) hn

  change M ≤ max (A n) (B n)

  exact hMLe.trans (le_of_lt hRLt)

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
      if F 1 n ≤ F 0 n then 0 else 1

  have hChosen :
      ∀ n : ℕ,
        F (q n) n = max (F 0 n) (F 1 n) := by
    intro n
    dsimp only [q]
    by_cases h : F 1 n ≤ F 0 n
    · simp only [if_pos h]
      exact (max_eq_left h).symm
    · simp only [if_neg h]
      have hReverse : F 0 n ≤ F 1 n :=
        le_of_lt (lt_of_not_ge h)
      exact (max_eq_right hReverse).symm

  have hChosenTop :
      Tendsto
        (fun n : ℕ => F (q n) n)
        atTop
        atTop := by
    simpa only [hChosen] using hMax

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q0 : Fin 2, q n = q0 :=
    Frequently.of_forall
      (fun n => ⟨q n, rfl⟩)

  obtain ⟨q0, hFrequently⟩ :=
    (Filter.frequently_exists).1 hFrequentlySome

  obtain ⟨s, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop hFrequently

  have hs : ∀ n : ℕ, n ≤ s n := by
    intro n
    exact hMono.le_apply

  have hsTop : Tendsto s atTop atTop :=
    hMono.tendsto_atTop

  have hTopBeforeRewrite :
      Tendsto
        (fun n : ℕ => F (q (s n)) (s n))
        atTop
        atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ => F q0 (s n))
        atTop
        atTop := by
    simpa only [hFixed] using hTopBeforeRewrite

  exact ⟨q0, s, hs, hsTop, hTop⟩

/-! ## Raw-L² product branch -/

/-- The two primitive raw-Fourier `L²` factors of the oriented Young pair. -/
noncomputable def h3TerminalFourthQForcingDerivativeRawL2FactorAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (q : Fin 2) : ℝ :=
  let F :=
    h3TerminalFourthQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k
  let G :=
    h3TerminalFourthQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l
  if q = 0 then
    ‖h3SpectralScalarRawFourierConjL2 F‖
  else
    ‖h3SpectralScalarRawFourierL2 G‖

theorem h3TerminalFourthQForcingDerivativeRawL2FactorAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (q : Fin 2) :
    0 ≤
      h3TerminalFourthQForcingDerivativeRawL2FactorAt
        hH3 hClass ht j o k l q := by
  unfold h3TerminalFourthQForcingDerivativeRawL2FactorAt
  dsimp only
  split_ifs <;> exact norm_nonneg _

theorem h3TerminalFourthQForcingDerivativeRawL2ProductAt_eq_factors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    h3TerminalFourthQForcingDerivativeRawL2ProductAt
        hH3 hClass ht j o k l
      =
    h3TerminalFourthQForcingDerivativeRawL2FactorAt
        hH3 hClass ht j o k l 0
      *
    h3TerminalFourthQForcingDerivativeRawL2FactorAt
        hH3 hClass ht j o k l 1 := by
  unfold h3TerminalFourthQForcingDerivativeRawL2ProductAt
  unfold h3TerminalFourthQForcingDerivativeRawL2FactorAt
  dsimp only
  norm_num

theorem exists_fixed_h3TerminalFourthQForcingDerivativeRawL2Factor_subsequence_of_product_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hProductTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeRawL2ProductAt
              hH3 hClass (hτ n) j o k l
        )
        atTop
        atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalFourthQForcingDerivativeRawL2FactorAt
                hH3 hClass (hτ (s n)) j o k l q
          )
          atTop
          atTop := by

  have hFactorProductTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeRawL2FactorAt
                hH3 hClass (hτ n) j o k l 0
              *
            h3TerminalFourthQForcingDerivativeRawL2FactorAt
              hH3 hClass (hτ n) j o k l 1
        )
        atTop
        atTop := by
    simpa only [
      ← h3TerminalFourthQForcingDerivativeRawL2ProductAt_eq_factors
    ] using hProductTop

  have hMaxTop :
      Tendsto
        (
          fun n : ℕ =>
            max
              (
                h3TerminalFourthQForcingDerivativeRawL2FactorAt
                  hH3 hClass (hτ n) j o k l 0
              )
              (
                h3TerminalFourthQForcingDerivativeRawL2FactorAt
                  hH3 hClass (hτ n) j o k l 1
              )
        )
        atTop
        atTop :=
    max_tendstoAtTop_of_mul_tendstoAtTop
      (fun n =>
        h3TerminalFourthQForcingDerivativeRawL2FactorAt
          hH3 hClass (hτ n) j o k l 0)
      (fun n =>
        h3TerminalFourthQForcingDerivativeRawL2FactorAt
          hH3 hClass (hτ n) j o k l 1)
      (fun n =>
        h3TerminalFourthQForcingDerivativeRawL2FactorAt_nonneg
          hH3 hClass (hτ n) j o k l 0)
      (fun n =>
        h3TerminalFourthQForcingDerivativeRawL2FactorAt_nonneg
          hH3 hClass (hτ n) j o k l 1)
      hFactorProductTop

  obtain ⟨q, s, hs, hsTop, hFactorTop⟩ :=
    exists_fixed_fin2_subsequence_of_max_tendstoAtTop
      (fun q n =>
        h3TerminalFourthQForcingDerivativeRawL2FactorAt
          hH3 hClass (hτ n) j o k l q)
      hMaxTop

  exact
    ⟨q, s, hs, hsTop, hTauTendsto.comp hsTop, hFactorTop⟩

/-! ## Moment / L¹ mixture branch -/

/--
The two Young products inside the order-ten moment/raw-`L¹` mixture.
Channel `0` is `M10(F) * L1(G)` and channel `1` is `L1(F) * M10(G)`.
-/
noncomputable def h3TerminalFourthQForcingDerivativeMomentL1ProductAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (q : Fin 2) : ℝ :=
  let F :=
    h3TerminalFourthQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k
  let G :=
    h3TerminalFourthQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l
  if q = 0 then
    h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
      *
    h3SpectralScalarRawFourierL1Mass G
  else
    h3SpectralScalarRawFourierL1Mass F
      *
    h3SpectralScalarRawFourierMomentMass (10 : ℝ) G

theorem h3TerminalFourthQForcingDerivativeMomentL1ProductAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (q : Fin 2) :
    0 ≤
      h3TerminalFourthQForcingDerivativeMomentL1ProductAt
        hH3 hClass ht j o k l q := by
  unfold h3TerminalFourthQForcingDerivativeMomentL1ProductAt
  dsimp only
  split_ifs
  · exact
      mul_nonneg
        (h3SpectralScalarRawFourierMomentMass_nonneg (10 : ℝ) _)
        (h3SpectralScalarRawFourierL1Mass_nonneg _)
  · exact
      mul_nonneg
        (h3SpectralScalarRawFourierL1Mass_nonneg _)
        (h3SpectralScalarRawFourierMomentMass_nonneg (10 : ℝ) _)

theorem h3FourierMomentSplitCoefficient_ten_pos :
    0 < h3FourierMomentSplitCoefficient (10 : ℝ) := by
  unfold h3FourierMomentSplitCoefficient
  exact
    Real.rpow_pos_of_pos
      (by norm_num)
      (10 : ℝ)

theorem h3TerminalFourthQForcingDerivativeMomentL1MixAt_eq_products
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    h3TerminalFourthQForcingDerivativeMomentL1MixAt
        hH3 hClass ht j o k l
      =
    h3FourierMomentSplitCoefficient (10 : ℝ)
      *
    (
      h3TerminalFourthQForcingDerivativeMomentL1ProductAt
          hH3 hClass ht j o k l 0
        +
      h3TerminalFourthQForcingDerivativeMomentL1ProductAt
        hH3 hClass ht j o k l 1
    ) := by
  unfold h3TerminalFourthQForcingDerivativeMomentL1MixAt
  unfold h3TerminalFourthQForcingDerivativeMomentL1ProductAt
  dsimp only
  norm_num

theorem exists_fixed_h3TerminalFourthQForcingDerivativeMomentL1Product_subsequence_of_mix_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMixTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeMomentL1MixAt
              hH3 hClass (hτ n) j o k l
        )
        atTop
        atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalFourthQForcingDerivativeMomentL1ProductAt
                hH3 hClass (hτ (s n)) j o k l q
          )
          atTop
          atTop := by

  have hSumTop :
      Tendsto
        (
          fun n : ℕ =>
            h3FourierMomentSplitCoefficient (10 : ℝ)
              *
            (
              h3TerminalFourthQForcingDerivativeMomentL1ProductAt
                  hH3 hClass (hτ n) j o k l 0
                +
              h3TerminalFourthQForcingDerivativeMomentL1ProductAt
                hH3 hClass (hτ n) j o k l 1
            )
        )
        atTop
        atTop := by
    simpa only [
      ← h3TerminalFourthQForcingDerivativeMomentL1MixAt_eq_products
    ] using hMixTop

  have hMaxTop :
      Tendsto
        (
          fun n : ℕ =>
            max
              (
                h3TerminalFourthQForcingDerivativeMomentL1ProductAt
                  hH3 hClass (hτ n) j o k l 0
              )
              (
                h3TerminalFourthQForcingDerivativeMomentL1ProductAt
                  hH3 hClass (hτ n) j o k l 1
              )
        )
        atTop
        atTop :=
    max_tendstoAtTop_of_posConst_mul_add_tendstoAtTop
      (h3FourierMomentSplitCoefficient (10 : ℝ))
      (fun n =>
        h3TerminalFourthQForcingDerivativeMomentL1ProductAt
          hH3 hClass (hτ n) j o k l 0)
      (fun n =>
        h3TerminalFourthQForcingDerivativeMomentL1ProductAt
          hH3 hClass (hτ n) j o k l 1)
      h3FourierMomentSplitCoefficient_ten_pos
      hSumTop

  obtain ⟨q, s, hs, hsTop, hProductTop⟩ :=
    exists_fixed_fin2_subsequence_of_max_tendstoAtTop
      (fun q n =>
        h3TerminalFourthQForcingDerivativeMomentL1ProductAt
          hH3 hClass (hτ n) j o k l q)
      hMaxTop

  exact
    ⟨q, s, hs, hsTop, hTauTendsto.comp hsTop, hProductTop⟩

/-! ## Resolve a frozen group -/

theorem h3TerminalFourthQForcingDerivativeStateMassGroup_escape_resolves_factor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (q : Fin 2)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hGroupTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeStateMassGroupAt
              hH3 hClass (hτ n) j o k l q
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
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalFourthQForcingDerivativeRawL2FactorAt
                  hH3 hClass (hτ (s n)) j o k l r
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
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalFourthQForcingDerivativeMomentL1ProductAt
                  hH3 hClass (hτ (s n)) j o k l r
            )
            atTop
            atTop
    ) := by

  fin_cases q

  · have hRawTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalFourthQForcingDerivativeRawL2ProductAt
                hH3 hClass (hτ n) j o k l
          )
          atTop
          atTop := by
      simpa [
        h3TerminalFourthQForcingDerivativeStateMassGroupAt
      ] using hGroupTop

    exact
      Or.inl
        (
          exists_fixed_h3TerminalFourthQForcingDerivativeRawL2Factor_subsequence_of_product_tendstoAtTop
            hH3 hClass j o k l τ hτ hTauTendsto hRawTop
        )

  · have hMixTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalFourthQForcingDerivativeMomentL1MixAt
                hH3 hClass (hτ n) j o k l
          )
          atTop
          atTop := by
      simpa [
        h3TerminalFourthQForcingDerivativeStateMassGroupAt
      ] using hGroupTop

    exact
      Or.inr
        (
          exists_fixed_h3TerminalFourthQForcingDerivativeMomentL1Product_subsequence_of_mix_tendstoAtTop
            hH3 hClass j o k l τ hτ hTauTendsto hMixTop
        )

/--
Fourth-temporal escape now resolves to energy, a fixed nonzero higher-radial
moment, a fixed primitive raw-`L²` factor, or a fixed order-ten-moment/raw-`L¹`
Young product.
-/
theorem fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedForcingDerivativeStateMassFactor
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
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ => velocityH3EnergyAt u (τ (s n)))
          atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass m
                  (τ (s n))
                  (hτ (s n))
            )
            atTop (𝓝 ∞)
    )
      ∨
    (
      ∃ o : Fin 2,
        ∃ k l : Fin 3,
          (
            (
              ∃ r : Fin 2,
                ∃ s : ℕ → ℕ,
                  (∀ n : ℕ, n ≤ s n) ∧
                  Tendsto s atTop atTop ∧
                  Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
                  Tendsto
                    (
                      fun n : ℕ =>
                        h3TerminalFourthQForcingDerivativeRawL2FactorAt
                          hH3 hClass (hτ (s n)) j o k l r
                    )
                    atTop atTop
            )
              ∨
            (
              ∃ r : Fin 2,
                ∃ s : ℕ → ℕ,
                  (∀ n : ℕ, n ≤ s n) ∧
                  Tendsto s atTop atTop ∧
                  Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
                  Tendsto
                    (
                      fun n : ℕ =>
                        h3TerminalFourthQForcingDerivativeMomentL1ProductAt
                          hH3 hClass (hτ (s n)) j o k l r
                    )
                    atTop atTop
            )
          )
    ) := by

  rcases
    fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedForcingDerivativeStateMassGroup
      hH3 hClass j τ hτ hTauTendsto hFourth
  with
    hEnergy
    |
    hRest

  · exact Or.inl hEnergy

  · rcases hRest with
      hHigher
      |
      hGroup

    · exact Or.inr (Or.inl hHigher)

    · rcases hGroup with
        ⟨o, q, k, l, s, hs, hsTop, hTauSub, hGroupTop⟩

      rcases
        h3TerminalFourthQForcingDerivativeStateMassGroup_escape_resolves_factor
          hH3 hClass j o k l q
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

        have hComp : ∀ n : ℕ, n ≤ s (v n) := by
          intro n
          exact le_trans (hv n) (hs (v n))

        have hCompTop :
            Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
          hsTop.comp hvTop

        exact
          Or.inr
            (
              Or.inr
                ⟨
                  o,
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
            )

      · rcases hMomentL1 with
          ⟨r, v, hv, hvTop, hTauFinal, hProductTop⟩

        have hComp : ∀ n : ℕ, n ≤ s (v n) := by
          intro n
          exact le_trans (hv n) (hs (v n))

        have hCompTop :
            Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
          hsTop.comp hvTop

        exact
          Or.inr
            (
              Or.inr
                ⟨
                  o,
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
            )

end

end Euclidean
end Bridge
end PrimeTensor
