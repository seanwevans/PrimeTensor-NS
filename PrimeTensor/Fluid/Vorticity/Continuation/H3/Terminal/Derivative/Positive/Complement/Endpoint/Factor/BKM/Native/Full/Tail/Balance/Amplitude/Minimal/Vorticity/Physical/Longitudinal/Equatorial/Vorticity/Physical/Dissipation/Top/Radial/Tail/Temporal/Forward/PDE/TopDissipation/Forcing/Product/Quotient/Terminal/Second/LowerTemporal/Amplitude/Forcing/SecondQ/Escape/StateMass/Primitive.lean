import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.SecondQ.Escape.StateMass

/-!
# Freeze a primitive velocity mass in the second-q forcing-state envelope

The second-q forcing-state Young envelope contains six nonnegative primitive
velocity quantities:

1. raw conjugate `L²` mass of the first coordinate;
2. raw `L²` mass of the second coordinate;
3. moment-six mass of the first coordinate;
4. raw `L¹` mass of the second coordinate;
5. raw `L¹` mass of the first coordinate;
6. moment-six mass of the second coordinate.

At every strict time the complete envelope is bounded by a fixed coefficient
times the fourth power of the largest primitive factor.  Consequently escape
of a fixed state-mass envelope freezes one primitive factor on a cofinal
subsequence.

This file performs only that finite extraction.  The primitive factors are
classified in the next layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

noncomputable def h3TerminalForcingSecondQPrimitiveFactorAt
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
    h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U k),
    h3SpectralScalarRawFourierL1Mass (U l),
    h3SpectralScalarRawFourierL1Mass (U k),
    h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U l)
  ] q

theorem h3TerminalForcingSecondQPrimitiveFactorAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 6) :
    0 ≤
      h3TerminalForcingSecondQPrimitiveFactorAt
        hH3 hClass ht k l q := by

  fin_cases q <;>
    simp [
      h3TerminalForcingSecondQPrimitiveFactorAt,
      h3SpectralScalarRawFourierMomentMass_nonneg,
      h3SpectralScalarRawFourierL1Mass_nonneg
    ]

/--
At each strict time, the complete second-q velocity state-mass envelope is
bounded by a fixed coefficient times the fourth power of one maximizing
primitive factor.
-/
theorem exists_primitive_h3TerminalForcingSecondQStateMassEnvelopeAt_le_fixedCoefficient_mul_pow_four
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    ∃ q : Fin 6,
      h3TerminalForcingSecondQStateMassEnvelopeAt
          hH3 hClass ht k l
        ≤
      (
        2 * h3FourierMomentSplitCoefficient (6 : ℝ)
      )
        *
      (
        h3TerminalForcingSecondQPrimitiveFactorAt
          hH3 hClass ht k l q
      ) ^ 4 := by

  classical

  let f : Fin 6 → ℝ :=
    fun q =>
      h3TerminalForcingSecondQPrimitiveFactorAt
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

  let H : ℝ := f q

  have hH0 :
      0 ≤ H := by
    dsimp only [H, f]
    exact
      h3TerminalForcingSecondQPrimitiveFactorAt_nonneg
        hH3 hClass ht k l q

  have hL2K :
      ‖h3SpectralScalarRawFourierConjL2 (U k)‖ ≤ H := by
    have h := hqMax 0 (Finset.mem_univ _)
    simpa [
      H,
      f,
      U,
      htAbs,
      h3TerminalForcingSecondQPrimitiveFactorAt
    ] using h

  have hL2L :
      ‖h3SpectralScalarRawFourierL2 (U l)‖ ≤ H := by
    have h := hqMax 1 (Finset.mem_univ _)
    simpa [
      H,
      f,
      U,
      htAbs,
      h3TerminalForcingSecondQPrimitiveFactorAt
    ] using h

  have hM6K :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U k) ≤ H := by
    have h := hqMax 2 (Finset.mem_univ _)
    simpa [
      H,
      f,
      U,
      htAbs,
      h3TerminalForcingSecondQPrimitiveFactorAt
    ] using h

  have hL1L :
      h3SpectralScalarRawFourierL1Mass (U l) ≤ H := by
    have h := hqMax 3 (Finset.mem_univ _)
    simpa [
      H,
      f,
      U,
      htAbs,
      h3TerminalForcingSecondQPrimitiveFactorAt
    ] using h

  have hL1K :
      h3SpectralScalarRawFourierL1Mass (U k) ≤ H := by
    have h := hqMax 4 (Finset.mem_univ _)
    simpa [
      H,
      f,
      U,
      htAbs,
      h3TerminalForcingSecondQPrimitiveFactorAt
    ] using h

  have hM6L :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U l) ≤ H := by
    have h := hqMax 5 (Finset.mem_univ _)
    simpa [
      H,
      f,
      U,
      htAbs,
      h3TerminalForcingSecondQPrimitiveFactorAt
    ] using h

  have hL2K0 :
      0 ≤ ‖h3SpectralScalarRawFourierConjL2 (U k)‖ :=
    norm_nonneg _

  have hL2L0 :
      0 ≤ ‖h3SpectralScalarRawFourierL2 (U l)‖ :=
    norm_nonneg _

  have hM6K0 :
      0 ≤ h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U k) :=
    h3SpectralScalarRawFourierMomentMass_nonneg _ _

  have hM6L0 :
      0 ≤ h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U l) :=
    h3SpectralScalarRawFourierMomentMass_nonneg _ _

  have hL1K0 :
      0 ≤ h3SpectralScalarRawFourierL1Mass (U k) :=
    h3SpectralScalarRawFourierL1Mass_nonneg _

  have hL1L0 :
      0 ≤ h3SpectralScalarRawFourierL1Mass (U l) :=
    h3SpectralScalarRawFourierL1Mass_nonneg _

  have hC0 :
      0 ≤ h3FourierMomentSplitCoefficient (6 : ℝ) :=
    h3FourierMomentSplitCoefficient_nonneg (6 : ℝ)

  have hL2Product :
      ‖h3SpectralScalarRawFourierConjL2 (U k)‖
          *
        ‖h3SpectralScalarRawFourierL2 (U l)‖
        ≤
      H ^ 2 := by

    have hMul :
        ‖h3SpectralScalarRawFourierConjL2 (U k)‖
            *
          ‖h3SpectralScalarRawFourierL2 (U l)‖
          ≤
        H * H :=
      mul_le_mul
        hL2K
        hL2L
        hL2L0
        hH0

    simpa [pow_two] using hMul

  have hFirstMomentProduct :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U k)
          *
        h3SpectralScalarRawFourierL1Mass (U l)
        ≤
      H ^ 2 := by

    have hMul :
        h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U k)
            *
          h3SpectralScalarRawFourierL1Mass (U l)
          ≤
        H * H :=
      mul_le_mul
        hM6K
        hL1L
        hL1L0
        hH0

    simpa [pow_two] using hMul

  have hSecondMomentProduct :
      h3SpectralScalarRawFourierL1Mass (U k)
          *
        h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U l)
        ≤
      H ^ 2 := by

    have hMul :
        h3SpectralScalarRawFourierL1Mass (U k)
            *
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U l)
          ≤
        H * H :=
      mul_le_mul
        hL1K
        hM6L
        hM6L0
        hH0

    simpa [pow_two] using hMul

  have hMomentSum :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U k)
            *
          h3SpectralScalarRawFourierL1Mass (U l)
        +
      h3SpectralScalarRawFourierL1Mass (U k)
            *
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U l)
        ≤
      2 * H ^ 2 := by
    linarith

  have hWeightedMoment :
      h3FourierMomentSplitCoefficient (6 : ℝ)
          *
        (
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U k)
              *
            h3SpectralScalarRawFourierL1Mass (U l)
          +
          h3SpectralScalarRawFourierL1Mass (U k)
              *
            h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U l)
        )
        ≤
      h3FourierMomentSplitCoefficient (6 : ℝ)
          *
        (2 * H ^ 2) :=
    mul_le_mul_of_nonneg_left
      hMomentSum
      hC0

  have hWeightedMoment0 :
      0 ≤
        h3FourierMomentSplitCoefficient (6 : ℝ)
          *
        (
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U k)
              *
            h3SpectralScalarRawFourierL1Mass (U l)
          +
          h3SpectralScalarRawFourierL1Mass (U k)
              *
            h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U l)
        ) := by

    apply mul_nonneg hC0

    exact
      add_nonneg
        (mul_nonneg hM6K0 hL1L0)
        (mul_nonneg hL1K0 hM6L0)

  have hEnvelope :
      h3TerminalForcingSecondQStateMassEnvelopeAt
          hH3 hClass ht k l
        ≤
      H ^ 2
        *
      (
        h3FourierMomentSplitCoefficient (6 : ℝ)
          *
        (2 * H ^ 2)
      ) := by

    unfold h3TerminalForcingSecondQStateMassEnvelopeAt
    dsimp only [U, htAbs]

    exact
      mul_le_mul
        hL2Product
        hWeightedMoment
        hWeightedMoment0
        (sq_nonneg H)

  refine ⟨q, ?_⟩

  calc
    h3TerminalForcingSecondQStateMassEnvelopeAt
        hH3 hClass ht k l
        ≤
      H ^ 2
        *
      (
        h3FourierMomentSplitCoefficient (6 : ℝ)
          *
        (2 * H ^ 2)
      ) :=
      hEnvelope
    _ =
      (
        2 * h3FourierMomentSplitCoefficient (6 : ℝ)
      ) * H ^ 4 := by
      ring
    _ =
      (
        2 * h3FourierMomentSplitCoefficient (6 : ℝ)
      )
        *
      (
        h3TerminalForcingSecondQPrimitiveFactorAt
          hH3 hClass ht k l q
      ) ^ 4 := by
      rfl

/--
Escape of a fixed second-q velocity state-mass envelope freezes one of its six
primitive masses on a cofinal subsequence.
-/
theorem exists_fixed_h3TerminalForcingSecondQPrimitiveFactor_subsequence_of_stateMassEnvelope_tendstoAtTop
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
        (
          fun n : ℕ =>
            h3TerminalForcingSecondQStateMassEnvelopeAt
              hH3 hClass (hτ n) k l
        )
        atTop
        atTop) :
    ∃ q : Fin 6,
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
              h3TerminalForcingSecondQPrimitiveFactorAt
                hH3 hClass (hτ (s n)) k l q
          )
          atTop
          atTop := by

  classical

  have hChoice :
      ∀ n : ℕ,
        ∃ q : Fin 6,
          h3TerminalForcingSecondQStateMassEnvelopeAt
              hH3 hClass (hτ n) k l
            ≤
          (
            2 * h3FourierMomentSplitCoefficient (6 : ℝ)
          )
            *
          (
            h3TerminalForcingSecondQPrimitiveFactorAt
              hH3 hClass (hτ n) k l q
          ) ^ 4 := by

    intro n

    exact
      exists_primitive_h3TerminalForcingSecondQStateMassEnvelopeAt_le_fixedCoefficient_mul_pow_four
        hH3 hClass (hτ n) k l

  choose q hq using hChoice

  let C : ℝ :=
    2 * h3FourierMomentSplitCoefficient (6 : ℝ)

  have hC0 :
      0 ≤ C := by
    dsimp only [C]

    exact
      mul_nonneg
        (by norm_num)
        (h3FourierMomentSplitCoefficient_nonneg (6 : ℝ))

  have hChosenTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingSecondQPrimitiveFactorAt
              hH3 hClass (hτ n) k l (q n)
        )
        atTop
        atTop := by

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
          h3TerminalForcingSecondQStateMassEnvelopeAt
            hH3 hClass (hτ n) k l :=
      hEnvelopeTop.eventually
        (eventually_gt_atTop (C * R ^ 4 + 1))

    filter_upwards [hLarge] with n hn

    let P : ℝ :=
      h3TerminalForcingSecondQPrimitiveFactorAt
        hH3 hClass (hτ n) k l (q n)

    have hP0 :
        0 ≤ P := by
      dsimp only [P]
      exact
        h3TerminalForcingSecondQPrimitiveFactorAt_nonneg
          hH3 hClass (hτ n) k l (q n)

    have hBound :
        h3TerminalForcingSecondQStateMassEnvelopeAt
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
          h3TerminalForcingSecondQStateMassEnvelopeAt
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

  have hTauSub :
      Tendsto
        (fun n : ℕ => τ (s n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp hsTop

  have hTopBeforeRewrite :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingSecondQPrimitiveFactorAt
              hH3 hClass (hτ (s n)) k l (q (s n))
        )
        atTop
        atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingSecondQPrimitiveFactorAt
              hH3 hClass (hτ (s n)) k l q0
        )
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
      hTauSub,
      hTop
    ⟩

/--
Complete finite extraction from second-q forcing mass to one fixed primitive
velocity factor.
-/
theorem exists_fixed_h3TerminalForcingSecondQPrimitiveFactor_subsequence_of_massPath_tendstoAtTop
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
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationForcingSecondQMassPath
              hH3 hClass j (τ n)
        )
        atTop
        atTop) :
    ∃ k l : Fin 3,
      ∃ q : Fin 6,
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
                h3TerminalForcingSecondQPrimitiveFactorAt
                  hH3 hClass (hτ (s n)) k l q
            )
            atTop
            atTop := by

  obtain
    ⟨k, l, s, hs, hsTop, hTauSub, hEnvelopeTop⟩ :=
    exists_fixed_pair_subsequence_of_h3TerminalForcingSecondQMassPath_stateMassEnvelope_tendstoAtTop
      hH3 hClass j τ hτ hTauTendsto hMassTop

  obtain
    ⟨q, v, hv, hvTop, hTauFinal, hPrimitiveTop⟩ :=
    exists_fixed_h3TerminalForcingSecondQPrimitiveFactor_subsequence_of_stateMassEnvelope_tendstoAtTop
      hH3
      hClass
      k
      l
      (fun n : ℕ => τ (s n))
      (fun n : ℕ => hτ (s n))
      hTauSub
      hEnvelopeTop

  refine
    ⟨
      k,
      l,
      q,
      (fun n : ℕ => s (v n)),
      ?_,
      hsTop.comp hvTop,
      hTauFinal,
      hPrimitiveTop
    ⟩

  intro n

  exact
    le_trans
      (hv n)
      (hs (v n))

end

end Euclidean
end Bridge
end PrimeTensor
