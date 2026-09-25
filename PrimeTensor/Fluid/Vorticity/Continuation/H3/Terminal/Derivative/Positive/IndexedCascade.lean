import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.IndexedEnergySequence

/-!
# Indexed terminal H³ cascade

The positive-derivative terminal sequence already carries

    T - 1/(n+1) < σ_n < T,
    n < E'(σ_n),
    4 (n+1)^2 < K^2 E(σ_n).

The eventual top-order dissipation rate is sharper than the harmonic
corollary:

    1 ≤ B (T-t)^8 D₃(t)^3,

with the canonical midpoint coefficient

    B = 81 K^8 E₀(midpoint).

Once `σ_n` enters that late tail, its explicit terminal localization gives

    ((n+1) (T-σ_n))^8 < 1.

Multiplying the cubic dissipation rate by `(n+1)^8` therefore yields the
division-free indexed bound

    (n+1)^8 ≤ B D₃(σ_n)^3.

At the same times `E'(σ_n) > n ≥ 0`.  Exact balance and `D ≥ D₃` imply

    2 D₃(σ_n) ≤ -T_H3(σ_n),

so cubing gives the synchronized adverse-transport estimate

    8 (n+1)^8 ≤ B (-T_H3(σ_n))^3.

Thus one and the same terminal sequence carries explicit indexed lower rates
for energy, positive energy growth, top-order dissipation, and adverse
transport.

These remain necessary conditions on a hypothetical nonextension branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Under hypothetical nonextension, the localized positive-derivative sequence
can be chosen so that, eventually, both top-order dissipation and adverse
transport satisfy their sharp indexed cubic rates with the same canonical
midpoint coefficient.
-/
theorem exists_terminal_indexed_h3_cascade_of_noH3PathExtension
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
            ∧
          4 * ((n : ℝ) + 1) ^ 2
            <
          h3PathSqrtEnergyRiccatiCoefficient ^ 2
            *
          velocityH3EnergyAt u (σ n)
      )
        ∧
      Tendsto σ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            deriv (velocityH3EnergyAt u) (σ n)
        )
        atTop
        atTop
        ∧
      ∀ᶠ n : ℕ in atTop,
        (
          ((n : ℝ) + 1) ^ 8
            ≤
          (
            81
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 8
              *
            velocityH3Energy0At
              u
              (h3BKMKineticTailMidpoint a T)
          )
            *
          velocityH3Dissipation3At u (σ n) ^ 3
        )
          ∧
        (
          8 * ((n : ℝ) + 1) ^ 8
            ≤
          (
            81
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 8
              *
            velocityH3Energy0At
              u
              (h3BKMKineticTailMidpoint a T)
          )
            *
          (- velocityH3TransportDerivativeAt u (σ n)) ^ 3
        ) := by

  obtain
    ⟨σ, hσ, hSigmaTendsto, hDerivativeTendsto⟩ :=
    exists_deriv_blowupSequence_with_quadratic_energy_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  obtain
    ⟨c, hc, hRate⟩ :=
    exists_terminalTail_topH3DissipationRate_midpoint_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hSigmaAboveC :
      ∀ᶠ n : ℕ in atTop,
        c < σ n :=
    (tendsto_order.1 hSigmaTendsto).1
      c
      hc.2

  have hIndexedRates :
      ∀ᶠ n : ℕ in atTop,
        (
          ((n : ℝ) + 1) ^ 8
            ≤
          (
            81
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 8
              *
            velocityH3Energy0At
              u
              (h3BKMKineticTailMidpoint a T)
          )
            *
          velocityH3Dissipation3At u (σ n) ^ 3
        )
          ∧
        (
          8 * ((n : ℝ) + 1) ^ 8
            ≤
          (
            81
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 8
              *
            velocityH3Energy0At
              u
              (h3BKMKineticTailMidpoint a T)
          )
            *
          (- velocityH3TransportDerivativeAt u (σ n)) ^ 3
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

    have hDerivativeN :
        (n : ℝ)
          <
        deriv (velocityH3EnergyAt u) (σ n) :=
      (hσ n).2.2.1

    have hTailN :
        σ n ∈ Set.Ioo c T :=
      ⟨
        hcn,
        hClassN.2
      ⟩

    let B : ℝ :=
      81
        *
      h3PathSqrtEnergyRiccatiCoefficient ^ 8
        *
      velocityH3Energy0At
        u
        (h3BKMKineticTailMidpoint a T)

    have hE0 :
        0 ≤
        velocityH3Energy0At
          u
          (h3BKMKineticTailMidpoint a T) :=
      velocityH3Energy0At_nonneg
        u
        (h3BKMKineticTailMidpoint a T)

    have hB :
        0 ≤ B := by
      dsimp only [B]
      positivity

    have hD3 :
        0 ≤ velocityH3Dissipation3At u (σ n) :=
      velocityH3Dissipation3At_nonneg
        u
        (σ n)

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

    have hScaledDistancePow :
        (
          ((n : ℝ) + 1) * (T - σ n)
        ) ^ 8
          ≤
        1 := by

      have hStrict :
          (
            ((n : ℝ) + 1) * (T - σ n)
          ) ^ 8
            <
          (1 : ℝ) ^ 8 :=
        pow_lt_pow_left₀
          hScaledDistance
          hScaledDistanceNonneg
          (by norm_num)

      simpa using
        (le_of_lt hStrict)

    have hRateN :
        1
          ≤
        B
          *
        (T - σ n) ^ 8
          *
        velocityH3Dissipation3At u (σ n) ^ 3 := by

      dsimp only [B]

      convert
        hRate
          (σ n)
          hTailN
        using 1 <;>
        ring

    have hNatPowNonneg :
        0 ≤ ((n : ℝ) + 1) ^ 8 :=
      pow_nonneg
        (le_of_lt hNPos)
        8

    have hRateScaled :=
      mul_le_mul_of_nonneg_left
        hRateN
        hNatPowNonneg

    have hCoeffD3Nonneg :
        0
          ≤
        B * velocityH3Dissipation3At u (σ n) ^ 3 :=
      mul_nonneg
        hB
        (pow_nonneg hD3 3)

    have hContract :=
      mul_le_mul_of_nonneg_right
        hScaledDistancePow
        hCoeffD3Nonneg

    have hIndexedD3 :
        ((n : ℝ) + 1) ^ 8
          ≤
        B * velocityH3Dissipation3At u (σ n) ^ 3 := by

      calc
        ((n : ℝ) + 1) ^ 8
            =
          ((n : ℝ) + 1) ^ 8 * 1 := by
            ring

        _ ≤
          ((n : ℝ) + 1) ^ 8
            *
          (
            B
              *
            (T - σ n) ^ 8
              *
            velocityH3Dissipation3At u (σ n) ^ 3
          ) :=
          hRateScaled

        _ =
          (
            ((n : ℝ) + 1) * (T - σ n)
          ) ^ 8
            *
          (
            B * velocityH3Dissipation3At u (σ n) ^ 3
          ) := by
            ring

        _ ≤
          1
            *
          (
            B * velocityH3Dissipation3At u (σ n) ^ 3
          ) :=
          hContract

        _ =
          B * velocityH3Dissipation3At u (σ n) ^ 3 := by
            ring

    have hDerivativePositive :
        0 < deriv (velocityH3EnergyAt u) (σ n) := by

      have hnNonneg :
          0 ≤ (n : ℝ) :=
        Nat.cast_nonneg n

      exact
        lt_of_le_of_lt
          hnNonneg
          hDerivativeN

    have hTop :
        velocityH3Dissipation3At u (σ n)
          ≤
        velocityH3DissipationAt u (σ n) :=
      velocityH3Dissipation3At_le_dissipationAt
        u
        (σ n)

    have hBalance :=
      deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
        hH3
        hClass
        hClassN

    have hTwiceD3 :
        2 * velocityH3Dissipation3At u (σ n)
          ≤
        - velocityH3TransportDerivativeAt u (σ n) := by

      linarith

    have hTwiceD3Nonneg :
        0
          ≤
        2 * velocityH3Dissipation3At u (σ n) := by
      positivity

    have hCube :
        (
          2 * velocityH3Dissipation3At u (σ n)
        ) ^ 3
          ≤
        (- velocityH3TransportDerivativeAt u (σ n)) ^ 3 :=
      pow_le_pow_left₀
        hTwiceD3Nonneg
        hTwiceD3
        3

    have hCubeEight :
        8 * velocityH3Dissipation3At u (σ n) ^ 3
          ≤
        (- velocityH3TransportDerivativeAt u (σ n)) ^ 3 := by

      calc
        8 * velocityH3Dissipation3At u (σ n) ^ 3
            =
          (
            2 * velocityH3Dissipation3At u (σ n)
          ) ^ 3 := by
            ring

        _ ≤
          (- velocityH3TransportDerivativeAt u (σ n)) ^ 3 :=
          hCube

    have hIndexedScaled :=
      mul_le_mul_of_nonneg_left
        hIndexedD3
        (by norm_num : (0 : ℝ) ≤ 8)

    have hTransportScaled :=
      mul_le_mul_of_nonneg_left
        hCubeEight
        hB

    have hIndexedTransport :
        8 * ((n : ℝ) + 1) ^ 8
          ≤
        B * (- velocityH3TransportDerivativeAt u (σ n)) ^ 3 := by

      calc
        8 * ((n : ℝ) + 1) ^ 8
            ≤
          8
            *
          (
            B * velocityH3Dissipation3At u (σ n) ^ 3
          ) :=
          hIndexedScaled

        _ =
          B
            *
          (
            8 * velocityH3Dissipation3At u (σ n) ^ 3
          ) := by
            ring

        _ ≤
          B * (- velocityH3TransportDerivativeAt u (σ n)) ^ 3 :=
          hTransportScaled

    refine
      ⟨
        ?_,
        ?_
      ⟩

    · simpa only [B] using
        hIndexedD3

    · simpa only [B] using
        hIndexedTransport

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hDerivativeTendsto,
      hIndexedRates
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
