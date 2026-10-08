import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Freeze fourth-q forcing amplitude into one primitive velocity mass

The preceding checkpoint proves

    ‖q² F_j(U,U)‖₂
      ≤
    (2π)^4 * finite order-five convolution sum.

This file performs only finite extraction:

1. fourth-q forcing mass escape forces escape of the named radial-Leray
   envelope;
2. one fixed coordinate pair `(k,l)` carries an order-five convolution norm
   escape on a cofinal subsequence;
3. the squared convolution norm is controlled by the generic Young state-mass
   envelope with doubled moment `10`;
4. one of six primitive velocity masses is frozen on a further cofinal
   subsequence.

The six primitive masses are:

* raw `L²` of coordinate `k`;
* raw `L²` of coordinate `l`;
* raw moment `10` of coordinate `k`;
* raw `L¹` of coordinate `l`;
* raw `L¹` of coordinate `k`;
* raw moment `10` of coordinate `l`.

The common envelope, pair, and state-mass declarations are imported from the
active Escape/Pair/Bound chain. The six unique declarations below retain their
original statements; the fixed-pair cancellation uses positive-coefficient
weak monotonicity to avoid an unavailable strict-monotonicity instance. No primitive is classified here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalFourthQForcingPrimitive
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingPrimitive :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 2400000


/-! ## Fixed-pair extraction (retained API) -/

theorem exists_fixed_pair_subsequence_of_h3TerminalForcingFourthQMassPath_tendstoAtTop
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
          h3TerminalPhysicalTopDissipationForcingFourthQMassPath
            hH3 hClass j (τ n))
        atTop atTop) :
    ∃ k l : Fin 3,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hτ (s n)) k l)
          atTop atTop := by

  classical

  have hEnvelopeTop :=
    h3TerminalForcingFourthQRadialLerayEnvelopeAt_tendstoAtTop_of_massPath_tendstoAtTop
      hH3 hClass j τ hτ hMassTop

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

    obtain ⟨k, l, hkl⟩ :=
      exists_pair_h3TerminalForcingFourthQRadialLerayEnvelopeAt_le_fixedCoefficient_mul_productNorm
        hH3 hClass (hτ n) j

    exact ⟨(k, l), hkl⟩

  choose p hp using hChoice

  have hCPos :
      0 < h3TerminalForcingFourthQFixedPairCoefficient :=
    h3TerminalForcingFourthQFixedPairCoefficient_pos

  have hChosenTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingFourthQRadialProductNormAt
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
          h3TerminalForcingFourthQFixedPairCoefficient * R
            <
          h3TerminalForcingFourthQRadialLerayEnvelopeAt
            hH3 hClass (hτ n) j :=
      hEnvelopeTop.eventually
        (eventually_gt_atTop
          (h3TerminalForcingFourthQFixedPairCoefficient * R))

    filter_upwards [hLarge] with n hn

    have hBound := hp n

    have hScaled :
        h3TerminalForcingFourthQFixedPairCoefficient * R
          <
        h3TerminalForcingFourthQFixedPairCoefficient
          *
        h3TerminalForcingFourthQRadialProductNormAt
          hH3 hClass (hτ n) (p n).1 (p n).2 :=
      lt_of_lt_of_le hn hBound

    have hRLt :
        R
          <
        h3TerminalForcingFourthQRadialProductNormAt
          hH3 hClass (hτ n) (p n).1 (p n).2 := by

      by_contra hNot
      have hLe :
          h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hτ n) (p n).1 (p n).2 ≤ R :=
        le_of_not_gt hNot
      have hScaledLe :=
        mul_le_mul_of_nonneg_left hLe (le_of_lt hCPos)
      exact (not_lt_of_ge hScaledLe) hScaled

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
          h3TerminalForcingFourthQRadialProductNormAt
            hH3 hClass (hτ (s n))
            (p (s n)).1
            (p (s n)).2)
        atTop atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingFourthQRadialProductNormAt
            hH3 hClass (hτ (s n))
            p0.1 p0.2)
        atTop atTop := by

    simpa only [hFixed] using
      hTopBeforeRewrite

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


/-! ## Six primitive masses -/

noncomputable def h3TerminalForcingFourthQPrimitiveFactorAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 6) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  ![
    ‖h3SpectralScalarRawFourierConjL2 (U k)‖,
    ‖h3SpectralScalarRawFourierL2 (U l)‖,
    h3SpectralScalarRawFourierMomentMass (10 : ℝ) (U k),
    h3SpectralScalarRawFourierL1Mass (U l),
    h3SpectralScalarRawFourierL1Mass (U k),
    h3SpectralScalarRawFourierMomentMass (10 : ℝ) (U l)
  ] q

theorem h3TerminalForcingFourthQPrimitiveFactorAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 6) :
    0 ≤
      h3TerminalForcingFourthQPrimitiveFactorAt
        hH3 hClass ht k l q := by

  fin_cases q <;>
    simp [
      h3TerminalForcingFourthQPrimitiveFactorAt,
      h3SpectralScalarRawFourierMomentMass_nonneg,
      h3SpectralScalarRawFourierL1Mass_nonneg
    ]

theorem exists_primitive_h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt_le_fixedCoefficient_mul_pow_four
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    ∃ q : Fin 6,
      h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
          hH3 hClass ht k l
        ≤
      (
        2 * h3FourierMomentSplitCoefficient (10 : ℝ)
      )
        *
      (
        h3TerminalForcingFourthQPrimitiveFactorAt
          hH3 hClass ht k l q
      ) ^ 4 := by

  classical

  let f : Fin 6 → ℝ :=
    fun q =>
      h3TerminalForcingFourthQPrimitiveFactorAt
        hH3 hClass ht k l q

  have hUnivNonempty :
      (Finset.univ : Finset (Fin 6)).Nonempty :=
    ⟨0, Finset.mem_univ _⟩

  obtain ⟨q, _hqMem, hqMax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (Fin 6))
      f
      hUnivNonempty

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let F := U k
  let G := U l
  let H : ℝ := f q

  have hH0 :
      0 ≤ H := by
    dsimp only [H, f]
    exact
      h3TerminalForcingFourthQPrimitiveFactorAt_nonneg
        hH3 hClass ht k l q

  have hL2F :
      ‖h3SpectralScalarRawFourierConjL2 F‖ ≤ H := by
    have h := hqMax 0 (Finset.mem_univ _)
    simpa [
      H, f, F, U,
      h3TerminalForcingFourthQPrimitiveFactorAt
    ] using h

  have hL2G :
      ‖h3SpectralScalarRawFourierL2 G‖ ≤ H := by
    have h := hqMax 1 (Finset.mem_univ _)
    simpa [
      H, f, G, U,
      h3TerminalForcingFourthQPrimitiveFactorAt
    ] using h

  have hM10F :
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) F ≤ H := by
    have h := hqMax 2 (Finset.mem_univ _)
    simpa [
      H, f, F, U,
      h3TerminalForcingFourthQPrimitiveFactorAt
    ] using h

  have hL1G :
      h3SpectralScalarRawFourierL1Mass G ≤ H := by
    have h := hqMax 3 (Finset.mem_univ _)
    simpa [
      H, f, G, U,
      h3TerminalForcingFourthQPrimitiveFactorAt
    ] using h

  have hL1F :
      h3SpectralScalarRawFourierL1Mass F ≤ H := by
    have h := hqMax 4 (Finset.mem_univ _)
    simpa [
      H, f, F, U,
      h3TerminalForcingFourthQPrimitiveFactorAt
    ] using h

  have hM10G :
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) G ≤ H := by
    have h := hqMax 5 (Finset.mem_univ _)
    simpa [
      H, f, G, U,
      h3TerminalForcingFourthQPrimitiveFactorAt
    ] using h

  have hL2F0 :
      0 ≤ ‖h3SpectralScalarRawFourierConjL2 F‖ :=
    norm_nonneg _

  have hL2G0 :
      0 ≤ ‖h3SpectralScalarRawFourierL2 G‖ :=
    norm_nonneg _

  have hM10F0 :
      0 ≤ h3SpectralScalarRawFourierMomentMass (10 : ℝ) F :=
    h3SpectralScalarRawFourierMomentMass_nonneg _ _

  have hM10G0 :
      0 ≤ h3SpectralScalarRawFourierMomentMass (10 : ℝ) G :=
    h3SpectralScalarRawFourierMomentMass_nonneg _ _

  have hL1F0 :
      0 ≤ h3SpectralScalarRawFourierL1Mass F :=
    h3SpectralScalarRawFourierL1Mass_nonneg _

  have hL1G0 :
      0 ≤ h3SpectralScalarRawFourierL1Mass G :=
    h3SpectralScalarRawFourierL1Mass_nonneg _

  have hC0 :
      0 ≤ h3FourierMomentSplitCoefficient (10 : ℝ) :=
    h3FourierMomentSplitCoefficient_nonneg (10 : ℝ)

  have hL2Product :
      ‖h3SpectralScalarRawFourierConjL2 F‖
          *
        ‖h3SpectralScalarRawFourierL2 G‖
        ≤
      H ^ 2 := by

    have hMul :
        ‖h3SpectralScalarRawFourierConjL2 F‖
            *
          ‖h3SpectralScalarRawFourierL2 G‖
          ≤
        H * H :=
      mul_le_mul
        hL2F
        hL2G
        hL2G0
        hH0

    simpa [pow_two] using hMul

  have hFirstMomentProduct :
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
          *
        h3SpectralScalarRawFourierL1Mass G
        ≤
      H ^ 2 := by

    have hMul :
        h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
            *
          h3SpectralScalarRawFourierL1Mass G
          ≤
        H * H :=
      mul_le_mul
        hM10F
        hL1G
        hL1G0
        hH0

    simpa [pow_two] using hMul

  have hSecondMomentProduct :
      h3SpectralScalarRawFourierL1Mass F
          *
        h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
        ≤
      H ^ 2 := by

    have hMul :
        h3SpectralScalarRawFourierL1Mass F
            *
          h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
          ≤
        H * H :=
      mul_le_mul
        hL1F
        hM10G
        hM10G0
        hH0

    simpa [pow_two] using hMul

  have hMomentSum :
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
            *
          h3SpectralScalarRawFourierL1Mass G
        +
      h3SpectralScalarRawFourierL1Mass F
            *
          h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
        ≤
      2 * H ^ 2 := by
    linarith

  have hWeightedMoment :
      h3FourierMomentSplitCoefficient (10 : ℝ)
          *
        (
          h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
              *
            h3SpectralScalarRawFourierL1Mass G
          +
          h3SpectralScalarRawFourierL1Mass F
              *
            h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
        )
        ≤
      h3FourierMomentSplitCoefficient (10 : ℝ)
          *
        (2 * H ^ 2) :=
    mul_le_mul_of_nonneg_left
      hMomentSum
      hC0

  have hWeightedMoment0 :
      0 ≤
        h3FourierMomentSplitCoefficient (10 : ℝ)
          *
        (
          h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
              *
            h3SpectralScalarRawFourierL1Mass G
          +
          h3SpectralScalarRawFourierL1Mass F
              *
            h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
        ) := by

    apply mul_nonneg hC0

    exact
      add_nonneg
        (mul_nonneg hM10F0 hL1G0)
        (mul_nonneg hL1F0 hM10G0)

  have hEnvelope :
      h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
          hH3 hClass ht k l
        ≤
      H ^ 2
        *
      (
        h3FourierMomentSplitCoefficient (10 : ℝ)
          *
        (2 * H ^ 2)
      ) := by

    unfold h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
    dsimp only [F, G, U]

    exact
      mul_le_mul
        hL2Product
        hWeightedMoment
        hWeightedMoment0
        (sq_nonneg H)

  refine ⟨q, ?_⟩

  calc
    h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
        hH3 hClass ht k l
        ≤
      H ^ 2
        *
      (
        h3FourierMomentSplitCoefficient (10 : ℝ)
          *
        (2 * H ^ 2)
      ) :=
      hEnvelope
    _ =
      (
        2 * h3FourierMomentSplitCoefficient (10 : ℝ)
      ) * H ^ 4 := by
      ring
    _ =
      (
        2 * h3FourierMomentSplitCoefficient (10 : ℝ)
      )
        *
      (
        h3TerminalForcingFourthQPrimitiveFactorAt
          hH3 hClass ht k l q
      ) ^ 4 := by
      rfl

theorem exists_fixed_h3TerminalForcingFourthQPrimitiveFactor_subsequence_of_stateMassEnvelope_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hEnvelopeTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
            hH3 hClass (hτ n) k l)
        atTop atTop) :
    ∃ q : Fin 6,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingFourthQPrimitiveFactorAt
              hH3 hClass (hτ (s n)) k l q)
          atTop atTop := by

  classical

  have hChoice :
      ∀ n : ℕ,
        ∃ q : Fin 6,
          h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
              hH3 hClass (hτ n) k l
            ≤
          (
            2 * h3FourierMomentSplitCoefficient (10 : ℝ)
          )
            *
          (
            h3TerminalForcingFourthQPrimitiveFactorAt
              hH3 hClass (hτ n) k l q
          ) ^ 4 := by

    intro n

    exact
      exists_primitive_h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt_le_fixedCoefficient_mul_pow_four
        hH3 hClass (hτ n) k l

  choose q hq using hChoice

  let C : ℝ :=
    2 * h3FourierMomentSplitCoefficient (10 : ℝ)

  have hC0 :
      0 ≤ C := by
    dsimp only [C]
    exact
      mul_nonneg
        (by norm_num)
        (h3FourierMomentSplitCoefficient_nonneg (10 : ℝ))

  have hChosenTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingFourthQPrimitiveFactorAt
            hH3 hClass (hτ n) k l (q n))
        atTop atTop := by

    refine tendsto_atTop.2 ?_

    intro M

    let R : ℝ := max M 1

    have hMLe :
        M ≤ R := by
      dsimp only [R]
      exact le_max_left M 1

    have hR0 :
        0 ≤ R := by
      dsimp only [R]
      exact
        le_trans
          (by norm_num)
          (le_max_right M 1)

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          C * R ^ 4 + 1
            <
          h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
            hH3 hClass (hτ n) k l :=
      hEnvelopeTop.eventually
        (eventually_gt_atTop (C * R ^ 4 + 1))

    filter_upwards [hLarge] with n hn

    let P : ℝ :=
      h3TerminalForcingFourthQPrimitiveFactorAt
        hH3 hClass (hτ n) k l (q n)

    have hP0 :
        0 ≤ P := by
      dsimp only [P]
      exact
        h3TerminalForcingFourthQPrimitiveFactorAt_nonneg
          hH3 hClass (hτ n) k l (q n)

    have hBound :
        h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
            hH3 hClass (hτ n) k l
          ≤
        C * P ^ 4 := by
      dsimp only [C, P]
      exact hq n

    have hRLtP :
        R < P := by

      by_contra hNot

      have hPLe :
          P ≤ R :=
        le_of_not_gt hNot

      have hPowLe :
          P ^ 4 ≤ R ^ 4 :=
        pow_le_pow_left₀ hP0 hPLe 4

      have hScaled :
          C * P ^ 4 ≤ C * R ^ 4 :=
        mul_le_mul_of_nonneg_left
          hPowLe
          hC0

      have hEnvelopeLe :
          h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
              hH3 hClass (hτ n) k l
            ≤
          C * R ^ 4 :=
        hBound.trans hScaled

      linarith

    exact
      hMLe.trans
        (le_of_lt hRLtP)

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q0 : Fin 6,
          q n = q0 :=
    Frequently.of_forall
      (fun n => ⟨q n, rfl⟩)

  obtain ⟨q0, hFrequently⟩ :=
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
          h3TerminalForcingFourthQPrimitiveFactorAt
            hH3 hClass (hτ (s n)) k l (q (s n)))
        atTop atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingFourthQPrimitiveFactorAt
            hH3 hClass (hτ (s n)) k l q0)
        atTop atTop := by
    simpa only [hFixed] using
      hTopBeforeRewrite

  exact
    ⟨
      q0,
      s,
      hs,
      hsTop,
      hTauTendsto.comp hsTop,
      hTop
    ⟩

/--
Complete finite extraction for fourth-q forcing amplitude escape: after two
cofinal subsequence extractions, one fixed pair `(k,l)` and one fixed primitive
index `q : Fin 6` carry the escape.
-/
theorem exists_fixed_h3TerminalForcingFourthQPrimitiveFactor_subsequence_of_massPath_tendstoAtTop
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
          h3TerminalPhysicalTopDissipationForcingFourthQMassPath
            hH3 hClass j (τ n))
        atTop atTop) :
    ∃ k l : Fin 3,
      ∃ q : Fin 6,
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalForcingFourthQPrimitiveFactorAt
                hH3 hClass (hτ (s n)) k l q)
            atTop atTop := by

  obtain
    ⟨k, l, s, hs, hsTop, hTauSub, hPairTop⟩ :=
    exists_fixed_pair_subsequence_of_h3TerminalForcingFourthQMassPath_tendstoAtTop
      hH3 hClass j τ hτ hTauTendsto hMassTop

  have hStateEnvelopeTop :=
    h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
      hH3 hClass k l
      (fun n : ℕ => τ (s n))
      (fun n : ℕ => hτ (s n))
      hPairTop

  obtain
    ⟨q, v, hv, hvTop, hTauFinal, hPrimitiveTop⟩ :=
    exists_fixed_h3TerminalForcingFourthQPrimitiveFactor_subsequence_of_stateMassEnvelope_tendstoAtTop
      hH3 hClass k l
      (fun n : ℕ => τ (s n))
      (fun n : ℕ => hτ (s n))
      hTauSub
      hStateEnvelopeTop

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
    ⟨
      k,
      l,
      q,
      (fun n : ℕ => s (v n)),
      hComp,
      hCompTop,
      hTauFinal,
      hPrimitiveTop
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
