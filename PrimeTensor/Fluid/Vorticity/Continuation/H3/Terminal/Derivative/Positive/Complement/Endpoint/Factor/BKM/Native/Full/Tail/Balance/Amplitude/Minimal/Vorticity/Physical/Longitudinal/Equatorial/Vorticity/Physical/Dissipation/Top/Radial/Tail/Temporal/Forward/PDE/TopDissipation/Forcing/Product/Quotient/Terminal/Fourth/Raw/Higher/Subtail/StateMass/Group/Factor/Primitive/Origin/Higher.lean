import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Subtail.StateMass.Group.Factor.Primitive.Origin
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Absorb the fourth-q velocity moment-ten obstruction

After primitive-origin classification, only one velocity-side obstruction
remains: the terminal raw Fourier moment of order ten.

There is no need to build a second radial hierarchy for this lower moment.
Pointwise,

    |ξ|^10 ≤ 1 + |ξ|^14.

Hence the order-ten moment is controlled by the raw `L¹` mass plus the
already-classified order-fourteen moment.  Escape therefore forces either:

* raw `L¹` escape, which is already physical H³-energy escape; or
* order-fourteen moment escape, which the existing third-q radial machinery
  already absorbs into an extended higher-radial moment.

The resulting fourth-temporal frontier contains only physical H³ energy,
extended higher-radial moments, or primitive masses of the projected-RHS
state `R`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000

/--
Use exactly the finite-axis instance chosen by the generic Fourier-moment
algebra so the moment weights and raw `L¹` package remain definitionally
aligned.
-/
noncomputable local instance axisFintypeH3TerminalFourthQVelocityMomentTenHigher
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

noncomputable local instance point3MeasureSpaceH3TerminalFourthQVelocityMomentTenHigher :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3TerminalFourthQVelocityMomentTenHigher Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Order ten is controlled by raw L¹ plus order fourteen -/

theorem norm_pow_ten_le_one_add_pow_fourteen
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 10 ≤ 1 + ‖ξ‖ ^ 14 := by

  have hx0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  by_cases hx1 : ‖ξ‖ ≤ 1

  · have hpow :
        ‖ξ‖ ^ 10 ≤ (1 : ℝ) ^ 10 :=
      pow_le_pow_left₀ hx0 hx1 10

    have hpowOne :
        ‖ξ‖ ^ 10 ≤ 1 := by
      simpa using hpow

    have h14 :
        0 ≤ ‖ξ‖ ^ 14 :=
      pow_nonneg hx0 14

    linarith

  · have hx1' :
        1 ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hx1)

    have hfour :
        (1 : ℝ) ^ 4 ≤ ‖ξ‖ ^ 4 :=
      pow_le_pow_left₀
        (by norm_num : 0 ≤ (1 : ℝ))
        hx1'
        4

    have hfour' :
        1 ≤ ‖ξ‖ ^ 4 := by
      simpa using hfour

    have hten0 :
        0 ≤ ‖ξ‖ ^ 10 :=
      pow_nonneg hx0 10

    have hmul :=
      mul_le_mul_of_nonneg_left
        hfour'
        hten0

    have htenfourteen :
        ‖ξ‖ ^ 10 ≤ ‖ξ‖ ^ 14 := by
      calc
        ‖ξ‖ ^ 10
            =
          ‖ξ‖ ^ 10 * 1 := by ring
        _ ≤
          ‖ξ‖ ^ 10 * ‖ξ‖ ^ 4 := hmul
        _ =
          ‖ξ‖ ^ 14 := by ring

    exact
      le_add_of_nonneg_of_le
        zero_le_one
        htenfourteen

/--
A finite order-fourteen raw Fourier moment controls the order-ten moment by
the unweighted raw `L¹` mass plus the order-fourteen mass.
-/
theorem h3SpectralScalarRawFourierMomentMass_ten_le_L1Mass_add_fourteen
    (H : H3SpectralScalarState)
    (hH14 : H3RawFourierMomentIntegrable (14 : ℝ) H) :
    h3SpectralScalarRawFourierMomentMass (10 : ℝ) H
      ≤
    h3SpectralScalarRawFourierL1Mass H
      +
    h3SpectralScalarRawFourierMomentMass (14 : ℝ) H := by

  have hWeight10 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (10 : ℝ) ξ = ‖ξ‖ ^ 10 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 10 ξ

  have hWeight14 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (14 : ℝ) ξ = ‖ξ‖ ^ 14 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 14 ξ

  have hRaw0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 H)

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier H)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3TerminalFourthQVelocityMomentTenHigher,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRaw0

  have hRawNorm :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRaw.norm

  have hH14' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 14 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by

    unfold H3RawFourierMomentIntegrable at hH14

    refine hH14.congr ?_

    filter_upwards with ξ

    rw [hWeight14 ξ]

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3SpectralScalarRawFourier H ξ‖
        +
      ‖ξ‖ ^ 14 *
        ‖h3SpectralScalarRawFourier H ξ‖

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by
    dsimp only [major]
    exact hRawNorm.add hH14'

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 10 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by

    exact
      ((continuous_norm.pow 10).aestronglyMeasurable.mul
        hRawNorm.aestronglyMeasurable)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 10 *
            ‖h3SpectralScalarRawFourier H ξ‖
          ≤
        major ξ := by

    intro ξ

    have hWeight :=
      norm_pow_ten_le_one_add_pow_fourteen ξ

    have hNorm0 :
        0 ≤ ‖h3SpectralScalarRawFourier H ξ‖ :=
      norm_nonneg _

    have hMul :=
      mul_le_mul_of_nonneg_right
        hWeight
        hNorm0

    dsimp only [major]

    calc
      ‖ξ‖ ^ 10 *
          ‖h3SpectralScalarRawFourier H ξ‖
          ≤
        (1 + ‖ξ‖ ^ 14) *
          ‖h3SpectralScalarRawFourier H ξ‖ :=
        hMul
      _ =
        ‖h3SpectralScalarRawFourier H ξ‖
          +
        ‖ξ‖ ^ 14 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
        ring

  have hLeft :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 10 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by

    refine hMajor.mono' hLeftMeas ?_

    filter_upwards with ξ

    have hNonneg :
        0 ≤
          ‖ξ‖ ^ 10 *
            ‖h3SpectralScalarRawFourier H ξ‖ :=
      mul_nonneg
        (pow_nonneg (norm_nonneg ξ) 10)
        (norm_nonneg _)

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hNonneg
    ] using hPoint ξ

  have hInt :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 10 *
          ‖h3SpectralScalarRawFourier H ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by

    apply integral_mono_ae hLeft hMajor

    filter_upwards with ξ

    exact hPoint ξ

  have hMass10 :
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 10 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by

    unfold h3SpectralScalarRawFourierMomentMass

    apply integral_congr_ae

    filter_upwards with ξ

    rw [hWeight10 ξ]

  have hMass14 :
      h3SpectralScalarRawFourierMomentMass (14 : ℝ) H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 14 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by

    unfold h3SpectralScalarRawFourierMomentMass

    apply integral_congr_ae

    filter_upwards with ξ

    rw [hWeight14 ξ]

  have hMass0 :
      h3SpectralScalarRawFourierL1Mass H
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier H ξ‖ := by

    unfold h3SpectralScalarRawFourierL1Mass

    simp only [
      axisFintypeH3TerminalFourthQVelocityMomentTenHigher,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ]

  have hMajorIntegral :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      h3SpectralScalarRawFourierL1Mass H
        +
      h3SpectralScalarRawFourierMomentMass (14 : ℝ) H := by

    dsimp only [major]

    rw [integral_add hRawNorm hH14']

    rw [hMass0, hMass14]

  rw [hMass10]

  rw [hMajorIntegral] at hInt

  exact hInt

theorem h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt_le_rawL1_add_moment14
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3) :
    h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
        hH3 hClass ht i
      ≤
    h3TerminalForcingThirdQRawL1MassAt
        hH3 hClass ht i
      +
    h3TerminalForcingThirdQMoment14MassAt
      hH3 hClass ht i := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hH14 :
      H3RawFourierMomentIntegrable
        (14 : ℝ)
        (U i) := by

    dsimp only [U]

    exact
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
        hH3 hClass ht 14 (by norm_num) i

  have hBound :=
    h3SpectralScalarRawFourierMomentMass_ten_le_L1Mass_add_fourteen
      (U i)
      hH14

  unfold
    h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
    h3TerminalForcingThirdQRawL1MassAt
    h3TerminalForcingThirdQMoment14MassAt

  dsimp only [U, htAbs] at hBound ⊢

  exact hBound

/-! ## Escape transfer to raw L¹ or the already-closed order-fourteen branch -/

theorem h3TerminalFourthQForcingDerivativeVelocityMoment10Max_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i)
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        max
          (h3TerminalForcingThirdQRawL1MassAt
            hH3 hClass (hτ n) i)
          (h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) i))
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
        h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
          hH3 hClass (hτ n) i :=
    hMomentTop.eventually
      (eventually_gt_atTop (2 * R + 1))

  filter_upwards [hLarge] with n hn

  let A : ℝ :=
    h3TerminalForcingThirdQRawL1MassAt
      hH3 hClass (hτ n) i

  let B : ℝ :=
    h3TerminalForcingThirdQMoment14MassAt
      hH3 hClass (hτ n) i

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

  have hBound :=
    h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt_le_rawL1_add_moment14
      hH3 hClass (hτ n) i

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

    have hMomentLe :
        h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i
          ≤
        2 * R := by
      dsimp only [A, B] at hBound hSum
      exact hBound.trans hSum

    linarith

  change
    M ≤
      max
        (h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass (hτ n) i)
        (h3TerminalForcingThirdQMoment14MassAt
          hH3 hClass (hτ n) i)

  exact
    hMLe.trans
      (le_of_lt hRLtH)

noncomputable def h3TerminalFourthQForcingDerivativeVelocityMoment10ResolverAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3)
    (q : Fin 2) : ℝ :=
  if q = 0 then
    h3TerminalForcingThirdQRawL1MassAt
      hH3 hClass ht i
  else
    h3TerminalForcingThirdQMoment14MassAt
      hH3 hClass ht i

theorem exists_fixed_h3TerminalFourthQForcingDerivativeVelocityMoment10Resolver_subsequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i)
        atTop atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeVelocityMoment10ResolverAt
              hH3 hClass (hτ (s n)) i q)
          atTop atTop := by

  classical

  have hMaxTop :=
    h3TerminalFourthQForcingDerivativeVelocityMoment10Max_tendstoAtTop
      hH3 hClass i τ hτ hMomentTop

  let q : ℕ → Fin 2 :=
    fun n =>
      if
        h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) i
          ≤
        h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass (hτ n) i
      then 0
      else 1

  have hChosen :
      ∀ n : ℕ,
        h3TerminalFourthQForcingDerivativeVelocityMoment10ResolverAt
            hH3 hClass (hτ n) i (q n)
          =
        max
          (h3TerminalForcingThirdQRawL1MassAt
            hH3 hClass (hτ n) i)
          (h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) i) := by

    intro n

    dsimp only [q]

    by_cases h :
        h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) i
          ≤
        h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass (hτ n) i

    · simp only [if_pos h]

      unfold h3TerminalFourthQForcingDerivativeVelocityMoment10ResolverAt

      simp only [if_pos]

      exact
        (max_eq_left h).symm

    · simp only [if_neg h]

      have hReverse :
          h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass (hτ n) i
            ≤
          h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) i :=
        le_of_lt
          (lt_of_not_ge h)

      unfold h3TerminalFourthQForcingDerivativeVelocityMoment10ResolverAt

      simp only [if_neg, one_ne_zero]

      exact
        (max_eq_right hReverse).symm

  have hChosenTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeVelocityMoment10ResolverAt
            hH3 hClass (hτ n) i (q n))
        atTop atTop := by
    simpa only [hChosen] using hMaxTop

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

  have hTauSub :
      Tendsto
        (fun n : ℕ => τ (s n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp hsTop

  have hTopBeforeRewrite :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeVelocityMoment10ResolverAt
            hH3 hClass (hτ (s n)) i (q (s n)))
        atTop atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeVelocityMoment10ResolverAt
            hH3 hClass (hτ (s n)) i q0)
        atTop atTop := by
    simpa only [hFixed] using hTopBeforeRewrite

  exact
    ⟨q0, s, hs, hsTop, hTauSub, hTop⟩

/--
Velocity moment-ten escape is not a new obstruction: it refines to either
physical H³-energy escape or one already-existing nonzero extended
higher-radial moment.
-/
theorem h3TerminalFourthQForcingDerivativeVelocityMoment10_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
            hH3 hClass (hτ n) i)
        atTop atTop) :
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
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop (𝓝 ∞)
    ) := by

  obtain
    ⟨q, s, hs, hsTop, hTauSub, hResolverTop⟩ :=
    exists_fixed_h3TerminalFourthQForcingDerivativeVelocityMoment10Resolver_subsequence
      hH3 hClass i τ hτ hTauTendsto hMomentTop

  fin_cases q

  · have hL1Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass (hτ (s n)) i)
          atTop atTop := by

      simpa [
        h3TerminalFourthQForcingDerivativeVelocityMoment10ResolverAt
      ] using hResolverTop

    have hEnergyTop :=
      velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
        hH3 hClass i
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hL1Top

    exact
      Or.inl
        ⟨s, hs, hsTop, hTauSub, hEnergyTop⟩

  · have hMoment14Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingThirdQMoment14MassAt
              hH3 hClass (hτ (s n)) i)
          atTop atTop := by

      simpa [
        h3TerminalFourthQForcingDerivativeVelocityMoment10ResolverAt
      ] using hResolverTop

    obtain
      ⟨qRadial, v, hv, hvTop, hTauFinal, hSquareTop⟩ :=
      exists_fixed_h3TerminalForcingThirdQMoment14RadialSquareChannel_subsequence
        hH3 hClass i
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hTauSub
        hMoment14Top

    have hHigherTop :=
      h3TerminalForcingThirdQMoment14RadialSquareChannel_escape_resolves_higherRadial
        hH3 hClass i qRadial
        (fun n : ℕ => τ (s (v n)))
        (fun n : ℕ => hτ (s (v n)))
        hSquareTop

    have hComp :
        ∀ n : ℕ, n ≤ s (v n) := by
      intro n
      exact le_trans (hv n) (hs (v n))

    have hCompTop :
        Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
      hsTop.comp hvTop

    have hShiftNe :
        h3TerminalForcingThirdQHigherRadialShift qRadial ≠ 0 := by
      fin_cases qRadial <;>
        norm_num [h3TerminalForcingThirdQHigherRadialShift]

    exact
      Or.inr
        ⟨
          h3TerminalForcingThirdQHigherRadialShift qRadial,
          hShiftNe,
          (fun n : ℕ => s (v n)),
          hComp,
          hCompTop,
          hTauFinal,
          hHigherTop
        ⟩

/-! ## Projected-RHS-only residual obstruction -/

inductive H3TerminalFourthQForcingDerivativeProjectedRHSObstruction where
  | rawL2
  | moment10
  | rawL1
  deriving DecidableEq, Repr

noncomputable def h3TerminalFourthQForcingDerivativeProjectedRHSObstructionAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (c : H3TerminalFourthQForcingDerivativeProjectedRHSObstruction)
    (i : Fin 3) : ℝ :=
  match c with
  | .rawL2 =>
      h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
        hH3 hClass ht j i
  | .moment10 =>
      h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
        hH3 hClass ht j i
  | .rawL1 =>
      h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
        hH3 hClass ht j i

/--
After absorbing the final velocity moment-ten alternative, fourth-temporal
escape has only three structural outcomes: physical H³ energy, one fixed
nonzero extended higher-radial moment, or one fixed primitive projected-RHS
mass.
-/
theorem fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedProjectedRHSPrimitive
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
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop (𝓝 ∞)
    )
      ∨
    (
      ∃ c : H3TerminalFourthQForcingDerivativeProjectedRHSObstruction,
        ∃ i : Fin 3,
          ∃ s : ℕ → ℕ,
            (∀ n : ℕ, n ≤ s n) ∧
            Tendsto s atTop atTop ∧
            Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
            Tendsto
              (fun n : ℕ =>
                h3TerminalFourthQForcingDerivativeProjectedRHSObstructionAt
                  hH3 hClass (hτ (s n)) j c i)
              atTop atTop
    ) := by

  rcases
    fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedForcingDerivativePrimitiveObstruction
      hH3 hClass j τ hτ hTauTendsto hFourth
  with hEnergy | hRest

  · exact Or.inl hEnergy

  · rcases hRest with hHigher | hPrimitive

    · exact Or.inr (Or.inl hHigher)

    · rcases hPrimitive with
        ⟨c, i, s, hs, hsTop, hTauSub, hPrimitiveTop⟩

      cases c with

      | velocityMoment10 =>

          have hMomentTop :
              Tendsto
                (fun n : ℕ =>
                  h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
                    hH3 hClass (hτ (s n)) i)
                atTop atTop := by

            simpa [
              h3TerminalFourthQForcingDerivativePrimitiveObstructionAt
            ] using hPrimitiveTop

          rcases
            h3TerminalFourthQForcingDerivativeVelocityMoment10_escape_energy_or_fixedExtendedHigherRadial
              hH3 hClass i
              (fun n : ℕ => τ (s n))
              (fun n : ℕ => hτ (s n))
              hTauSub
              hMomentTop
          with hEnergySub | hHigherSub

          · rcases hEnergySub with
              ⟨v, hv, hvTop, hTauFinal, hEnergyTop⟩

            have hComp :
                ∀ n : ℕ, n ≤ s (v n) := by
              intro n
              exact le_trans (hv n) (hs (v n))

            have hCompTop :
                Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
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
                ∀ n : ℕ, n ≤ s (v n) := by
              intro n
              exact le_trans (hv n) (hs (v n))

            have hCompTop :
                Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
              hsTop.comp hvTop

            exact
              Or.inr
                (
                  Or.inl
                    ⟨
                      m,
                      hm,
                      (fun n : ℕ => s (v n)),
                      hComp,
                      hCompTop,
                      hTauFinal,
                      hHigherTop
                    ⟩
                )

      | projectedRHSRawL2 =>

          exact
            Or.inr
              (
                Or.inr
                  ⟨
                    .rawL2,
                    i,
                    s,
                    hs,
                    hsTop,
                    hTauSub,
                    by
                      simpa [
                        h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                        h3TerminalFourthQForcingDerivativeProjectedRHSObstructionAt
                      ] using hPrimitiveTop
                  ⟩
              )

      | projectedRHSMoment10 =>

          exact
            Or.inr
              (
                Or.inr
                  ⟨
                    .moment10,
                    i,
                    s,
                    hs,
                    hsTop,
                    hTauSub,
                    by
                      simpa [
                        h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                        h3TerminalFourthQForcingDerivativeProjectedRHSObstructionAt
                      ] using hPrimitiveTop
                  ⟩
              )

      | projectedRHSRawL1 =>

          exact
            Or.inr
              (
                Or.inr
                  ⟨
                    .rawL1,
                    i,
                    s,
                    hs,
                    hsTop,
                    hTauSub,
                    by
                      simpa [
                        h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                        h3TerminalFourthQForcingDerivativeProjectedRHSObstructionAt
                      ] using hPrimitiveTop
                  ⟩
              )

end

end Euclidean
end Bridge
end PrimeTensor
