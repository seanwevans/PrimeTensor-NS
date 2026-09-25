import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicFrequencyRate

/-!
# Quantitative terminal collapse of the characteristic top-order length

The characteristic top-order frequency and reciprocal length are

    Λ₃(t) = sqrt(D₃(t) / E₃(t)),
    ℓ₃(t) = Λ₃(t)⁻¹.

The preceding terminal frequency theorem gives, on a sufficiently late tail,

    1
      ≤
    C(t) Λ₃(t)^6,

where

    C(t) =
      3 K^2 (E₀(b)+1) (T-t)^2.

Since the inequality itself forces `Λ₃(t) ≠ 0`, multiplication by
`ℓ₃(t)^6 = Λ₃(t)^(-6)` gives the exact dual estimate

    ℓ₃(t)^6
      ≤
    3 K^2 (E₀(b)+1) (T-t)^2.

Thus hypothetical nonextension forces the characteristic top-order length to
collapse at least on the `(T-t)^(1/3)` scale, stated without fractional powers.

On the existing localized positive-derivative sequence

    T - 1/(n+1) < σ_n < T,

the same estimate yields, eventually,

    (n+1)^2 ℓ₃(σ_n)^6
      ≤
    3 K^2 (E₀(midpoint)+1).

This remains a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Algebraic duality between frequency and length sixth-power rates -/

/--
Any sixth-power lower bound for the characteristic frequency transfers exactly
to the reciprocal characteristic length:

    1 ≤ C Λ₃(t)^6  ->  ℓ₃(t)^6 ≤ C.
-/
theorem h3TopCharacteristicLengthAt_pow_six_le_of_one_le_mul_frequency_pow_six
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t C : ℝ}
    (hRate :
      1
        ≤
      C * h3TopCharacteristicFrequencyAt u t ^ 6) :
    h3TopCharacteristicLengthAt u t ^ 6
      ≤
    C := by

  have hFrequencyNe :
      h3TopCharacteristicFrequencyAt u t ≠ 0 := by

    intro hZero

    rw [hZero] at hRate

    norm_num at hRate

  have hLengthNonneg :
      0 ≤ h3TopCharacteristicLengthAt u t := by

    unfold h3TopCharacteristicLengthAt

    exact
      inv_nonneg.mpr
        (h3TopCharacteristicFrequencyAt_nonneg
          u t)

  have hLengthPowNonneg :
      0 ≤ h3TopCharacteristicLengthAt u t ^ 6 :=
    pow_nonneg
      hLengthNonneg
      6

  have hProduct :
      h3TopCharacteristicFrequencyAt u t ^ 6
          *
        h3TopCharacteristicLengthAt u t ^ 6
        =
      1 := by

    unfold h3TopCharacteristicLengthAt

    rw [inv_pow]

    exact
      mul_inv_cancel₀
        (pow_ne_zero
          6
          hFrequencyNe)

  have hScaled :=
    mul_le_mul_of_nonneg_right
      hRate
      hLengthPowNonneg

  calc
    h3TopCharacteristicLengthAt u t ^ 6
        =
      1 * h3TopCharacteristicLengthAt u t ^ 6 := by
        ring

    _ ≤
      (
        C * h3TopCharacteristicFrequencyAt u t ^ 6
      )
        *
      h3TopCharacteristicLengthAt u t ^ 6 :=
      hScaled

    _ =
      C
        *
      (
        h3TopCharacteristicFrequencyAt u t ^ 6
          *
        h3TopCharacteristicLengthAt u t ^ 6
      ) := by
        ring

    _ =
      C := by
        rw [hProduct, mul_one]

/-! ## Terminal-distance length scale -/

/--
On a sufficiently late terminal interval, hypothetical nonextension forces

    ℓ₃(t)^6
      ≤
    3 K² (E₀(b)+1) (T-t)^2.
-/
theorem exists_terminalTail_characteristicLength_pow_six_le_terminalDistance_sq_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        h3TopCharacteristicLengthAt u t ^ 6
          ≤
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (
          velocityH3Energy0At u b
            +
          1
        )
          *
        (T - t) ^ 2 := by

  obtain
    ⟨c, hc, hFrequencyRate⟩ :=
    exists_terminalTail_characteristicFrequency_pow_six_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  refine
    ⟨
      c,
      hc,
      ?_
    ⟩

  intro t ht

  let C : ℝ :=
    3
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 2
      *
    (
      velocityH3Energy0At u b
        +
      1
    )
      *
    (T - t) ^ 2

  have hRateC :
      1
        ≤
      C * h3TopCharacteristicFrequencyAt u t ^ 6 := by

    dsimp only [C]

    simpa only [mul_assoc] using
      hFrequencyRate
        t
        ht

  have hLength :=
    h3TopCharacteristicLengthAt_pow_six_le_of_one_le_mul_frequency_pow_six
      hRateC

  simpa only [C] using
    hLength

/--
Canonical midpoint-anchor specialization of the terminal characteristic length
collapse.
-/
theorem exists_terminalTail_characteristicLength_pow_six_le_terminalDistance_sq_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ c : ℝ,
      c ∈
        Set.Ioo
          (h3BKMKineticTailMidpoint a T)
          T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        h3TopCharacteristicLengthAt u t ^ 6
          ≤
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (
          velocityH3Energy0At
              u
              (h3BKMKineticTailMidpoint a T)
            +
          1
        )
          *
        (T - t) ^ 2 := by

  exact
    exists_terminalTail_characteristicLength_pow_six_le_terminalDistance_sq_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

/-! ## Indexed length collapse on the localized cascade sequence -/

/--
On the localized positive-derivative terminal cascade sequence, the sixth power
of the characteristic length satisfies the eventual indexed estimate

    (n+1)^2 ℓ₃(σ_n)^6
      ≤
    3 K² (E₀(midpoint)+1).
-/
theorem exists_terminal_characteristicLength_indexed_collapse_sequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ σ : ℕ → ℝ,
      (
        ∀ n : ℕ,
          σ n ∈ Set.Ioo a T
            ∧
          σ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          (n : ℝ)
            <
          deriv (velocityH3EnergyAt u) (σ n)
      )
        ∧
      Tendsto σ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicLengthAt u (σ n)
        )
        atTop
        (𝓝 0)
        ∧
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 2
            *
          h3TopCharacteristicLengthAt u (σ n) ^ 6
          ≤
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (
          velocityH3Energy0At
              u
              (h3BKMKineticTailMidpoint a T)
            +
          1
        ) := by

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      _hE3Tendsto,
      _hFrequencyTendsto,
      hLengthTendsto
    ⟩ :=
    exists_terminal_characteristicFrequencyCascade_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  obtain
    ⟨c, hc, hLengthRate⟩ :=
    exists_terminalTail_characteristicLength_pow_six_le_terminalDistance_sq_midpoint_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hSigmaAboveC :
      ∀ᶠ n : ℕ in atTop,
        c < σ n :=
    (tendsto_order.1 hSigmaTendsto).1
      c
      hc.2

  have hIndexed :
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 2
            *
          h3TopCharacteristicLengthAt u (σ n) ^ 6
          ≤
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (
          velocityH3Energy0At
              u
              (h3BKMKineticTailMidpoint a T)
            +
          1
        ) := by

    filter_upwards
      [hSigmaAboveC]
      with n hcn

    have hClassN :
        σ n ∈ Set.Ioo a T :=
      (hσ n).1

    have hNearN :
        σ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T :=
      (hσ n).2.1

    have hTailN :
        σ n ∈ Set.Ioo c T :=
      ⟨
        hcn,
        hClassN.2
      ⟩

    let C0 : ℝ :=
      3
        *
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (
        velocityH3Energy0At
            u
            (h3BKMKineticTailMidpoint a T)
          +
        1
      )

    have hE0 :
        0 ≤
        velocityH3Energy0At
          u
          (h3BKMKineticTailMidpoint a T) :=
      velocityH3Energy0At_nonneg
        u
        (h3BKMKineticTailMidpoint a T)

    have hC0 :
        0 ≤ C0 := by

      dsimp only [C0]

      positivity

    have hLengthN :
        h3TopCharacteristicLengthAt u (σ n) ^ 6
          ≤
        C0 * (T - σ n) ^ 2 := by

      dsimp only [C0]

      simpa only [mul_assoc] using
        hLengthRate
          (σ n)
          hTailN

    have hNPos :
        0 < (n : ℝ) + 1 := by
      positivity

    have hDistancePos :
        0 < T - σ n := by
      linarith [hNearN.2]

    have hDistanceUpper :
        T - σ n
          <
        1 / ((n : ℝ) + 1) := by
      linarith [hNearN.1]

    have hScaledDistanceRaw :
        ((n : ℝ) + 1) * (T - σ n)
          <
        ((n : ℝ) + 1)
          * (1 / ((n : ℝ) + 1)) :=
      mul_lt_mul_of_pos_left
        hDistanceUpper
        hNPos

    have hCancel :
        ((n : ℝ) + 1)
          * (1 / ((n : ℝ) + 1))
          =
        1 := by

      rw [one_div]

      exact
        mul_inv_cancel₀
          (ne_of_gt hNPos)

    have hScaledDistance :
        ((n : ℝ) + 1) * (T - σ n)
          <
        1 :=
      lt_of_lt_of_eq
        hScaledDistanceRaw
        hCancel

    have hScaledDistanceNonneg :
        0
          ≤
        ((n : ℝ) + 1) * (T - σ n) := by
      positivity

    have hScaledDistanceSq :
        (
          ((n : ℝ) + 1) * (T - σ n)
        ) ^ 2
          ≤
        1 := by

      have hStrict :
          (
            ((n : ℝ) + 1) * (T - σ n)
          ) ^ 2
            <
          (1 : ℝ) ^ 2 :=
        pow_lt_pow_left₀
          hScaledDistance
          hScaledDistanceNonneg
          (by norm_num)

      simpa using
        (le_of_lt hStrict)

    have hNatSqNonneg :
        0 ≤ ((n : ℝ) + 1) ^ 2 := by
      positivity

    have hScaledLength :=
      mul_le_mul_of_nonneg_left
        hLengthN
        hNatSqNonneg

    have hContract :=
      mul_le_mul_of_nonneg_left
        hScaledDistanceSq
        hC0

    have hFinal :
        ((n : ℝ) + 1) ^ 2
            *
          h3TopCharacteristicLengthAt u (σ n) ^ 6
          ≤
        C0 := by

      calc
        ((n : ℝ) + 1) ^ 2
            *
          h3TopCharacteristicLengthAt u (σ n) ^ 6
            ≤
          ((n : ℝ) + 1) ^ 2
            *
          (
            C0 * (T - σ n) ^ 2
          ) :=
          hScaledLength

        _ =
          C0
            *
          (
            ((n : ℝ) + 1) * (T - σ n)
          ) ^ 2 := by
            ring

        _ ≤
          C0 * 1 :=
          hContract

        _ =
          C0 := by
            ring

    simpa only [C0] using
      hFinal

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hLengthTendsto,
      hIndexed
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
