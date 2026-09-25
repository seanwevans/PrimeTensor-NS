import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.SuperquadraticCascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.MomentCauchy

/-!
# Terminal top-order frequency cascade

The preceding indexed cascade measures top dissipation and adverse transport
against the auxiliary sequence index.  The Fourier interpolation theorem lets
us make a more intrinsic comparison against the actual third-order H³ energy.

On every strict H³ energy-class slice,

    E₃(t)^4 ≤ E₀(t) D₃(t)^3.

The kinetic energy `E₀` is antitone on the path tail, while hypothetical
nonextension forces the third-order block `E₃` to carry an inverse-square
terminal lower rate after one late restart.

Synchronizing that rate with the positive-derivative sequence gives

    E₃(σ_n) -> +∞.

Now fix any `M > 0`.  Once

    E₃(σ_n) > (E₀(b) + 1) M^3,

the interpolation inequality and the tail kinetic bound imply

    (M E₃(σ_n))^3 < D₃(σ_n)^3,

hence

    M E₃(σ_n) < D₃(σ_n).

Therefore

    D₃(σ_n) / E₃(σ_n) -> +∞.

Since full dissipation dominates `D₃`, and positive energy growth together
with exact balance gives

    -T_H3(σ_n) ≥ 2 D₃(σ_n),

the same sequence also satisfies

    D(σ_n) / E₃(σ_n) -> +∞,

and

    (-T_H3(σ_n)) / E₃(σ_n) -> +∞.

Thus the hypothetical nonextension branch forces an intrinsic top-order
frequency cascade: dissipation grows without bound relative to the top-order
energy itself.

This remains a necessary-condition theorem and does not assert existence of a
nonextendible path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Eventual indexed E₃ rate on the localized derivative sequence -/

/--
Along the localized positive-derivative sequence, the third-order H³ energy
eventually satisfies the indexed inverse-square lower rate

    (n+1)^2 ≤ 3 K^2 E₃(σ_n).
-/
theorem exists_deriv_blowupSequence_eventually_indexed_energy3_rate_of_noH3PathExtension
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
            deriv (velocityH3EnergyAt u) (σ n)
        )
        atTop
        atTop
        ∧
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 2
          ≤
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        velocityH3Energy3At u (σ n) := by

  obtain
    ⟨σ, hσFull, hSigmaTendsto, hDerivativeTendsto⟩ :=
    exists_deriv_blowupSequence_with_quadratic_energy_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hσ :
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
        deriv (velocityH3EnergyAt u) (σ n) := by

    intro n

    exact
      ⟨
        (hσFull n).1,
        (hσFull n).2.1,
        (hσFull n).2.2.1
      ⟩

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  obtain
    ⟨c, hc, hLate⟩ :=
    exists_terminalTail_kineticAnchorTerm_le_three
      u
      T
      b
      hb.2

  have hSigmaAboveC :
      ∀ᶠ n : ℕ in atTop,
        c < σ n :=
    (tendsto_order.1 hSigmaTendsto).1
      c
      hc.2

  have hIndexedE3 :
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 2
          ≤
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        velocityH3Energy3At u (σ n) := by

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

    have hAnchorN :
        σ n ∈ Set.Ioo b T :=
      ⟨
        lt_trans hc.1 hcn,
        hClassN.2
      ⟩

    have hRate :
        1
          ≤
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (T - σ n) ^ 2
          *
        velocityH3Energy3At u (σ n) :=
      one_le_three_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_energy3_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hb
        hAnchorN
        (hLate (σ n) hTailN)

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

    have hCoeffNonneg :
        0
          ≤
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        velocityH3Energy3At u (σ n) := by

      have hE3 :
          0 ≤ velocityH3Energy3At u (σ n) :=
        velocityH3Energy3At_nonneg
          u
          (σ n)

      positivity

    have hRateScaled :=
      mul_le_mul_of_nonneg_left
        hRate
        (by positivity :
          0 ≤ ((n : ℝ) + 1) ^ 2)

    have hContract :=
      mul_le_mul_of_nonneg_right
        hScaledDistanceSq
        hCoeffNonneg

    calc
      ((n : ℝ) + 1) ^ 2
          =
        ((n : ℝ) + 1) ^ 2 * 1 := by
          ring

      _ ≤
        ((n : ℝ) + 1) ^ 2
          *
        (
          3
            *
          h3PathSqrtEnergyRiccatiCoefficient ^ 2
            *
          (T - σ n) ^ 2
            *
          velocityH3Energy3At u (σ n)
        ) :=
        hRateScaled

      _ =
        (
          ((n : ℝ) + 1) * (T - σ n)
        ) ^ 2
          *
        (
          3
            *
          h3PathSqrtEnergyRiccatiCoefficient ^ 2
            *
          velocityH3Energy3At u (σ n)
        ) := by
          ring

      _ ≤
        1
          *
        (
          3
            *
          h3PathSqrtEnergyRiccatiCoefficient ^ 2
            *
          velocityH3Energy3At u (σ n)
        ) :=
        hContract

      _ =
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        velocityH3Energy3At u (σ n) := by
          ring

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hDerivativeTendsto,
      hIndexedE3
    ⟩

/-! ## E₃ divergence on the same sequence -/

/--
The same localized positive-derivative sequence has third-order H³ energy
tending to `+∞`.
-/
theorem exists_deriv_blowupSequence_with_energy3_tendsto_atTop_of_noH3PathExtension
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
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop := by

  obtain
    ⟨σ, hσ, hSigmaTendsto, _hDerivativeTendsto, hIndexedE3⟩ :=
    exists_deriv_blowupSequence_eventually_indexed_energy3_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  let C : ℝ :=
    3
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 2

  have hCPos :
      0 < C := by

    dsimp only [C]

    exact
      mul_pos
        (by norm_num : (0 : ℝ) < 3)
        (pow_pos
          h3PathSqrtEnergyRiccatiCoefficient_pos
          2)

  have hE3Tendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    let Q : ℝ :=
      max M 0

    obtain
      ⟨N : ℕ, hN⟩ :=
      exists_nat_gt
        (C * Q)

    filter_upwards
      [
        hIndexedE3,
        eventually_ge_atTop N
      ]
      with n hRateN hn

    have hCast :
        (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn

    have hCQltN :
        C * Q < (n : ℝ) :=
      lt_of_lt_of_le
        hN
        hCast

    have hnNonneg :
        0 ≤ (n : ℝ) :=
      Nat.cast_nonneg n

    have hnLeSq :
        (n : ℝ)
          ≤
        ((n : ℝ) + 1) ^ 2 := by
      nlinarith
        [sq_nonneg (n : ℝ)]

    have hCQ :
        C * Q
          <
        ((n : ℝ) + 1) ^ 2 :=
      lt_of_lt_of_le
        hCQltN
        hnLeSq

    have hCE3 :
        C * Q
          <
        C * velocityH3Energy3At u (σ n) :=
      lt_of_lt_of_le
        hCQ
        (by
          simpa only [C] using hRateN)

    have hQE3 :
        Q < velocityH3Energy3At u (σ n) :=
      lt_of_mul_lt_mul_left
        hCE3
        (le_of_lt hCPos)

    have hMQ :
        M ≤ Q := by

      dsimp only [Q]

      exact
        le_max_left
          M
          0

    exact
      le_of_lt
        (lt_of_le_of_lt
          hMQ
          hQE3)

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hE3Tendsto
    ⟩

/-! ## Intrinsic frequency cascade D₃ / E₃ -/

/--
Along the same positive-derivative terminal sequence,

    D₃(σ_n) / E₃(σ_n) -> +∞.

This is an intrinsic top-order frequency-cascade statement.
-/
theorem exists_terminal_dissipation3_over_energy3_tendsto_atTop_of_noH3PathExtension
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
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Dissipation3At u (σ n)
              /
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop := by

  obtain
    ⟨σ, hσ, hSigmaTendsto, hE3Tendsto⟩ :=
    exists_deriv_blowupSequence_with_energy3_tendsto_atTop_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  have hKineticAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3
      hClass

  have hSigmaAboveB :
      ∀ᶠ n : ℕ in atTop,
        b < σ n :=
    (tendsto_order.1 hSigmaTendsto).1
      b
      hb.2

  have hRatioTendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Dissipation3At u (σ n)
              /
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    by_cases hM :
        M ≤ 0

    · filter_upwards [] with n

      have hD3 :
          0 ≤ velocityH3Dissipation3At u (σ n) :=
        velocityH3Dissipation3At_nonneg
          u
          (σ n)

      have hE3 :
          0 ≤ velocityH3Energy3At u (σ n) :=
        velocityH3Energy3At_nonneg
          u
          (σ n)

      exact
        le_trans
          hM
          (div_nonneg hD3 hE3)

    · have hMPos :
          0 < M :=
        lt_of_not_ge
          hM

      let Q : ℝ :=
        (
          velocityH3Energy0At u b
            +
          1
        )
          *
        M ^ 3

      have hQPos :
          0 < Q := by

        have hE0 :
            0 ≤ velocityH3Energy0At u b :=
          velocityH3Energy0At_nonneg
            u b

        dsimp only [Q]

        positivity

      have hE3Large :
          ∀ᶠ n : ℕ in atTop,
            Q < velocityH3Energy3At u (σ n) :=
        hE3Tendsto.eventually
          (eventually_gt_atTop Q)

      filter_upwards
        [
          hE3Large,
          hSigmaAboveB
        ]
        with n hLarge hbn

      have hClassN :
          σ n ∈ Set.Ioo a T :=
        (hσ n).1

      have hAnchorN :
          σ n ∈ Set.Ioo b T :=
        ⟨
          hbn,
          hClassN.2
        ⟩

      have hE0Bound :
          velocityH3Energy0At u (σ n)
            ≤
          velocityH3Energy0At u b :=
        hKineticAnti
          hb
          hClassN
          (le_of_lt hbn)

      have hInterpolation :=
        velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
          hH3
          hClass
          hClassN

      have hE3Nonneg :
          0 ≤ velocityH3Energy3At u (σ n) :=
        velocityH3Energy3At_nonneg
          u
          (σ n)

      have hE3Pos :
          0 < velocityH3Energy3At u (σ n) :=
        lt_trans
          hQPos
          hLarge

      have hD3Nonneg :
          0 ≤ velocityH3Dissipation3At u (σ n) :=
        velocityH3Dissipation3At_nonneg
          u
          (σ n)

      have hE0PlusPos :
          0 < velocityH3Energy0At u b + 1 := by

        have hE0 :
            0 ≤ velocityH3Energy0At u b :=
          velocityH3Energy0At_nonneg
            u b

        linarith

      have hD3CubeNonneg :
          0 ≤ velocityH3Dissipation3At u (σ n) ^ 3 :=
        pow_nonneg
          hD3Nonneg
          3

      have hInterpolationAnchor :
          velocityH3Energy3At u (σ n) ^ 4
            ≤
          (
            velocityH3Energy0At u b
              +
            1
          )
            *
          velocityH3Dissipation3At u (σ n) ^ 3 := by

        calc
          velocityH3Energy3At u (σ n) ^ 4
              ≤
            velocityH3Energy0At u (σ n)
              *
            velocityH3Dissipation3At u (σ n) ^ 3 :=
            hInterpolation

          _ ≤
            velocityH3Energy0At u b
              *
            velocityH3Dissipation3At u (σ n) ^ 3 :=
            mul_le_mul_of_nonneg_right
              hE0Bound
              hD3CubeNonneg

          _ ≤
            (
              velocityH3Energy0At u b
                +
              1
            )
              *
            velocityH3Dissipation3At u (σ n) ^ 3 := by

            apply
              mul_le_mul_of_nonneg_right
                ?_
                hD3CubeNonneg

            linarith

      have hThreshold :
          (
            velocityH3Energy0At u b
              +
            1
          )
            *
          M ^ 3
            <
          velocityH3Energy3At u (σ n) := by

        simpa only [Q] using
          hLarge

      have hE3CubePos :
          0 < velocityH3Energy3At u (σ n) ^ 3 := by
        positivity

      have hThresholdScaled :
          (
            (
              velocityH3Energy0At u b
                +
              1
            )
              *
            M ^ 3
          )
            *
          velocityH3Energy3At u (σ n) ^ 3
            <
          velocityH3Energy3At u (σ n)
            *
          velocityH3Energy3At u (σ n) ^ 3 :=
        mul_lt_mul_of_pos_right
          hThreshold
          hE3CubePos

      have hLeftRearranged :
          (
            velocityH3Energy0At u b
              +
            1
          )
            *
          (
            M * velocityH3Energy3At u (σ n)
          ) ^ 3
            <
          velocityH3Energy3At u (σ n) ^ 4 := by

        calc
          (
            velocityH3Energy0At u b
              +
            1
          )
            *
          (
            M * velocityH3Energy3At u (σ n)
          ) ^ 3
              =
            (
              (
                velocityH3Energy0At u b
                  +
                1
              )
                *
              M ^ 3
            )
              *
            velocityH3Energy3At u (σ n) ^ 3 := by
                ring

          _ <
            velocityH3Energy3At u (σ n)
              *
            velocityH3Energy3At u (σ n) ^ 3 :=
            hThresholdScaled

          _ =
            velocityH3Energy3At u (σ n) ^ 4 := by
              ring

      have hWeightedCube :
          (
            velocityH3Energy0At u b
              +
            1
          )
            *
          (
            M * velocityH3Energy3At u (σ n)
          ) ^ 3
            <
          (
            velocityH3Energy0At u b
              +
            1
          )
            *
          velocityH3Dissipation3At u (σ n) ^ 3 :=
        lt_of_lt_of_le
          hLeftRearranged
          hInterpolationAnchor

      have hCube :
          (
            M * velocityH3Energy3At u (σ n)
          ) ^ 3
            <
          velocityH3Dissipation3At u (σ n) ^ 3 :=
        lt_of_mul_lt_mul_left
          hWeightedCube
          (le_of_lt hE0PlusPos)

      have hLinear :
          M * velocityH3Energy3At u (σ n)
            <
          velocityH3Dissipation3At u (σ n) :=
        lt_of_pow_lt_pow_left₀
          3
          hD3Nonneg
          hCube

      exact
        le_of_lt
          (
            (lt_div_iff₀ hE3Pos).2
              hLinear
          )

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hE3Tendsto,
      hRatioTendsto
    ⟩

/-! ## Full intrinsic terminal cascade -/

/--
The intrinsic terminal frequency cascade can be carried by one strict
positive-derivative sequence:

    E₃ -> +∞,
    D₃ / E₃ -> +∞,
    D / E₃ -> +∞,
    (-T_H3) / E₃ -> +∞.
-/
theorem exists_terminal_topFrequencyCascade_of_noH3PathExtension
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
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Dissipation3At u (σ n)
              /
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3DissipationAt u (σ n)
              /
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            (
              - velocityH3TransportDerivativeAt u (σ n)
            )
              /
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop := by

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hE3Tendsto,
      hD3RatioTendsto
    ⟩ :=
    exists_terminal_dissipation3_over_energy3_tendsto_atTop_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hFullRatioTendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3DissipationAt u (σ n)
              /
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hD3Eventually :
        ∀ᶠ n : ℕ in atTop,
          M
            ≤
          velocityH3Dissipation3At u (σ n)
            /
          velocityH3Energy3At u (σ n) :=
      hD3RatioTendsto.eventually
        (eventually_ge_atTop M)

    filter_upwards
      [hD3Eventually]
      with n hn

    have hE3 :
        0 ≤ velocityH3Energy3At u (σ n) :=
      velocityH3Energy3At_nonneg
        u
        (σ n)

    have hTop :
        velocityH3Dissipation3At u (σ n)
          ≤
        velocityH3DissipationAt u (σ n) :=
      velocityH3Dissipation3At_le_dissipationAt
        u
        (σ n)

    have hRatio :
        velocityH3Dissipation3At u (σ n)
            /
          velocityH3Energy3At u (σ n)
          ≤
        velocityH3DissipationAt u (σ n)
            /
          velocityH3Energy3At u (σ n) :=
      div_le_div_of_nonneg_right
        hTop
        hE3

    exact
      le_trans
        hn
        hRatio

  have hTransportRatioTendsto :
      Tendsto
        (
          fun n : ℕ =>
            (
              - velocityH3TransportDerivativeAt u (σ n)
            )
              /
            velocityH3Energy3At u (σ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hD3Eventually :
        ∀ᶠ n : ℕ in atTop,
          M
            ≤
          velocityH3Dissipation3At u (σ n)
            /
          velocityH3Energy3At u (σ n) :=
      hD3RatioTendsto.eventually
        (eventually_ge_atTop M)

    filter_upwards
      [hD3Eventually]
      with n hn

    have hClassN :
        σ n ∈ Set.Ioo a T :=
      (hσ n).1

    have hDerivativePositive :
        0
          <
        deriv (velocityH3EnergyAt u) (σ n) := by

      have hnNonneg :
          0 ≤ (n : ℝ) :=
        Nat.cast_nonneg n

      exact
        lt_of_le_of_lt
          hnNonneg
          (hσ n).2.2

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

    have hD3Nonneg :
        0 ≤ velocityH3Dissipation3At u (σ n) :=
      velocityH3Dissipation3At_nonneg
        u
        (σ n)

    have hTransportDom :
        velocityH3Dissipation3At u (σ n)
          ≤
        - velocityH3TransportDerivativeAt u (σ n) := by

      linarith

    have hE3 :
        0 ≤ velocityH3Energy3At u (σ n) :=
      velocityH3Energy3At_nonneg
        u
        (σ n)

    have hRatio :
        velocityH3Dissipation3At u (σ n)
            /
          velocityH3Energy3At u (σ n)
          ≤
        (
          - velocityH3TransportDerivativeAt u (σ n)
        )
            /
          velocityH3Energy3At u (σ n) :=
      div_le_div_of_nonneg_right
        hTransportDom
        hE3

    exact
      le_trans
        hn
        hRatio

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hE3Tendsto,
      hD3RatioTendsto,
      hFullRatioTendsto,
      hTransportRatioTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
