import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.AbsorptionDefectSequence

/-!
# Indexed energy growth along the positive-derivative terminal sequence

Hypothetical nonextension already forces the pointwise Riccati lower bound

    2 ≤ K (T-t) sqrt(E(t)).

Because the canonical H³ energy is positive, this can be squared without
changing the inequality:

    4 ≤ K^2 (T-t)^2 E(t).

The positive-derivative terminal sequence constructed earlier has the explicit
localization

    T - 1/(n+1) < σ_n < T.

Therefore

    T - σ_n < 1/(n+1),

and combining this with the Riccati lower bound yields the indexed estimate

    4 (n+1)^2 < K^2 E(σ_n).

Thus the same sequence on which

    E'(σ_n) -> +∞

also carries an explicit quadratic-in-index lower bound for the H³ energy.

This remains a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Squared Riccati energy rate -/

/--
Division-free squared form of the terminal Riccati lower bound:

    4 ≤ K² (T-t)² E(t).
-/
theorem four_le_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_energy_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    4
      ≤
    h3PathSqrtEnergyRiccatiCoefficient ^ 2
      *
    (T - t) ^ 2
      *
    velocityH3EnergyAt u t := by

  have hRate :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      ht

  have hE :
      0 ≤ velocityH3EnergyAt u t := by

    have hEOne :
        1 ≤ velocityH3EnergyAt u t :=
      one_le_velocityH3EnergyAt
        u t

    linarith

  have hRight :
      0
        ≤
      h3PathSqrtEnergyRiccatiCoefficient
        *
      (T - t)
        *
      Real.sqrt (velocityH3EnergyAt u t) := by
    positivity

  have hSquared :
      (2 : ℝ) ^ 2
        ≤
      (
        h3PathSqrtEnergyRiccatiCoefficient
          *
        (T - t)
          *
        Real.sqrt (velocityH3EnergyAt u t)
      ) ^ 2 :=

    (sq_le_sq₀
      (by norm_num : (0 : ℝ) ≤ 2)
      hRight).2
      hRate

  calc
    4
        =
      (2 : ℝ) ^ 2 := by
        norm_num

    _ ≤
      (
        h3PathSqrtEnergyRiccatiCoefficient
          *
        (T - t)
          *
        Real.sqrt (velocityH3EnergyAt u t)
      ) ^ 2 :=
      hSquared

    _ =
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (T - t) ^ 2
        *
      velocityH3EnergyAt u t := by

      rw [
        mul_pow,
        mul_pow,
        Real.sq_sqrt hE
      ]

/-! ## Indexed rate from explicit terminal localization -/

/--
If a strict terminal time lies inside the `1/(n+1)` left neighborhood of `T`,
then nonextension forces the explicit quadratic energy bound

    4 (n+1)^2 < K² E(t).
-/
theorem four_mul_natSucc_sq_lt_riccatiCoefficient_sq_mul_energy_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (n : ℕ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (htNear :
      t ∈
        Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1))
          T) :
    4 * ((n : ℝ) + 1) ^ 2
      <
    h3PathSqrtEnergyRiccatiCoefficient ^ 2
      *
    velocityH3EnergyAt u t := by

  have hRate :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      ht

  have hDen :
      0 < (n : ℝ) + 1 := by
    positivity

  have hDistanceUpper :
      T - t
        <
      1 / ((n : ℝ) + 1) := by
    linarith [htNear.1]

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt
      u t

  have hE :
      0 ≤ velocityH3EnergyAt u t := by
    linarith

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hSqrtPos :
      0 < Real.sqrt (velocityH3EnergyAt u t) :=
    Real.sqrt_pos.2
      hEPos

  have hKPos :
      0 < h3PathSqrtEnergyRiccatiCoefficient :=
    h3PathSqrtEnergyRiccatiCoefficient_pos

  have hKDistance :
      h3PathSqrtEnergyRiccatiCoefficient
          *
        (T - t)
        <
      h3PathSqrtEnergyRiccatiCoefficient
          *
        (1 / ((n : ℝ) + 1)) :=
    mul_lt_mul_of_pos_left
      hDistanceUpper
      hKPos

  have hProduct :
      h3PathSqrtEnergyRiccatiCoefficient
          *
        (T - t)
          *
        Real.sqrt (velocityH3EnergyAt u t)
        <
      h3PathSqrtEnergyRiccatiCoefficient
          *
        (1 / ((n : ℝ) + 1))
          *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_lt_mul_of_pos_right
      hKDistance
      hSqrtPos

  have hTwo :
      2
        <
      h3PathSqrtEnergyRiccatiCoefficient
          *
        (1 / ((n : ℝ) + 1))
          *
        Real.sqrt (velocityH3EnergyAt u t) :=
    lt_of_le_of_lt
      hRate
      hProduct

  have hScaled :=
    mul_lt_mul_of_pos_right
      hTwo
      hDen

  have hInvCancel :
      (1 / ((n : ℝ) + 1))
          *
        ((n : ℝ) + 1)
        =
      1 := by

    rw [one_div]

    exact
      inv_mul_cancel₀
        (ne_of_gt hDen)

  have hCancel :
      (
        h3PathSqrtEnergyRiccatiCoefficient
            *
          (1 / ((n : ℝ) + 1))
            *
          Real.sqrt (velocityH3EnergyAt u t)
      )
          *
        ((n : ℝ) + 1)
        =
      h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) := by

    calc
      (
        h3PathSqrtEnergyRiccatiCoefficient
            *
          (1 / ((n : ℝ) + 1))
            *
          Real.sqrt (velocityH3EnergyAt u t)
      )
          *
        ((n : ℝ) + 1)
          =
        h3PathSqrtEnergyRiccatiCoefficient
          *
        Real.sqrt (velocityH3EnergyAt u t)
          *
        (
          (1 / ((n : ℝ) + 1))
            *
          ((n : ℝ) + 1)
        ) := by
          ring

      _ =
        h3PathSqrtEnergyRiccatiCoefficient
          *
        Real.sqrt (velocityH3EnergyAt u t) := by
          rw [hInvCancel, mul_one]

  have hLinear :
      2 * ((n : ℝ) + 1)
        <
      h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) :=
    lt_of_lt_of_eq
      hScaled
      hCancel

  have hLeftNonneg :
      0 ≤ 2 * ((n : ℝ) + 1) := by
    positivity

  have hRightNonneg :
      0
        ≤
      h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) := by
    positivity

  have hSquared :
      (2 * ((n : ℝ) + 1)) ^ 2
        <
      (
        h3PathSqrtEnergyRiccatiCoefficient
          *
        Real.sqrt (velocityH3EnergyAt u t)
      ) ^ 2 :=
    (sq_lt_sq₀
      hLeftNonneg
      hRightNonneg).2
      hLinear

  calc
    4 * ((n : ℝ) + 1) ^ 2
        =
      (2 * ((n : ℝ) + 1)) ^ 2 := by
        ring

    _ <
      (
        h3PathSqrtEnergyRiccatiCoefficient
          *
        Real.sqrt (velocityH3EnergyAt u t)
      ) ^ 2 :=
      hSquared

    _ =
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      velocityH3EnergyAt u t := by

      rw [
        mul_pow,
        Real.sq_sqrt hE
      ]

/-! ## Synchronized derivative and energy sequence -/

/--
The positive-derivative terminal sequence can be chosen with its original
`1/(n+1)` localization and therefore carries an explicit quadratic H³-energy
lower rate at every index.
-/
theorem exists_deriv_blowupSequence_with_quadratic_energy_rate_of_noH3PathExtension
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
        atTop := by

  obtain
    ⟨σ, hσ, hSigmaTendsto, hDerivativeTendsto⟩ :=
    exists_deriv_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hIndexed :
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
        velocityH3EnergyAt u (σ n) := by

    intro n

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
      (hσ n).2.2

    have hEnergyN :
        4 * ((n : ℝ) + 1) ^ 2
          <
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        velocityH3EnergyAt u (σ n) :=
      four_mul_natSucc_sq_lt_riccatiCoefficient_sq_mul_energy_of_noH3PathExtension
        n
        hH3
        hNoExtension
        hClass
        hClassN
        hNearN

    exact
      ⟨
        hClassN,
        hNearN,
        hDerivativeN,
        hEnergyN
      ⟩

  exact
    ⟨
      σ,
      hIndexed,
      hSigmaTendsto,
      hDerivativeTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
