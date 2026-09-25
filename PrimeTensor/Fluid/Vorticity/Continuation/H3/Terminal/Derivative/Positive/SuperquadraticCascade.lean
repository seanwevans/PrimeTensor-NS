import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.IndexedCascade

/-!
# Superquadratic terminal dissipation and transport cascade

The indexed terminal cascade gives, eventually along one strict preterminal
sequence `σ_n -> T`,

    (n+1)^8 ≤ B D₃(σ_n)^3,

and

    8 (n+1)^8 ≤ B (-T_H3(σ_n))^3,

with one fixed nonnegative midpoint coefficient `B`.

These division-free cubic inequalities contain more asymptotic information
than ordinary divergence.  They force both `D₃` and adverse transport to grow
faster than every fixed multiple of `(n+1)^2`.

Indeed, if for some positive `M` one had

    f(n) < M (n+1)^2,

then

    B f(n)^3 < B M^3 (n+1)^6.

For sufficiently large `n`, the fixed coefficient `B M^3` is smaller than
`(n+1)^2`, making the right-hand side strictly smaller than `(n+1)^8`, which
contradicts the indexed cubic rate.

Hence

    D₃(σ_n) / (n+1)^2 -> +∞,

and

    (-T_H3(σ_n)) / (n+1)^2 -> +∞.

The canonical energy on the same sequence already has an explicit quadratic
lower bound, while top-order dissipation and adverse transport are forced to
be superquadratic in this sequence index.

These remain necessary consequences of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## A reusable cubic-rate to superquadratic-growth lemma -/

/--
An eventual indexed cubic lower rate

    (n+1)^8 ≤ B f(n)^3

with `B ≥ 0` and eventually nonnegative `f` forces

    f(n) / (n+1)^2 -> +∞.

Strict positivity of `B` need not be assumed: it follows from the rate itself.
-/
theorem tendsto_div_natSucc_sq_atTop_of_eventually_pow_eight_le_const_mul_cube
    {f : ℕ → ℝ}
    {B : ℝ}
    (hB : 0 ≤ B)
    (hf :
      ∀ᶠ n : ℕ in atTop,
        0 ≤ f n)
    (hRate :
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 8
          ≤
        B * (f n) ^ 3) :
    Tendsto
      (
        fun n : ℕ =>
          f n / ((n : ℝ) + 1) ^ 2
      )
      atTop
      atTop := by

  have hBPos :
      0 < B := by

    rcases eq_or_lt_of_le hB with hBZero | hBPositive

    · obtain
        ⟨n, hn⟩ :=
        hRate.exists

      have hPowPos :
          0 < ((n : ℝ) + 1) ^ 8 := by
        positivity

      rw [← hBZero, zero_mul] at hn

      linarith

    · exact hBPositive

  refine
    tendsto_atTop.2
      ?_

  intro M

  by_cases hM :
      M ≤ 0

  · filter_upwards
      [hf]
      with n hfn

    have hDenNonneg :
        0 ≤ ((n : ℝ) + 1) ^ 2 := by
      positivity

    have hRatioNonneg :
        0
          ≤
        f n / ((n : ℝ) + 1) ^ 2 :=
      div_nonneg
        hfn
        hDenNonneg

    exact
      le_trans
        hM
        hRatioNonneg

  · have hMPos :
        0 < M :=
      lt_of_not_ge
        hM

    obtain
      ⟨N : ℕ, hN⟩ :=
      exists_nat_gt
        (B * M ^ 3)

    filter_upwards
      [
        hf,
        hRate,
        eventually_ge_atTop N
      ]
      with n hfn hRateN hn

    have hCast :
        (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn

    have hBM3LtN :
        B * M ^ 3 < (n : ℝ) :=
      lt_of_lt_of_le
        hN
        hCast

    have hNatNonneg :
        0 ≤ (n : ℝ) :=
      Nat.cast_nonneg n

    have hDenPos :
        0 < ((n : ℝ) + 1) ^ 2 := by
      positivity

    apply
      (le_div_iff₀ hDenPos).2

    by_contra hNot

    have hfLt :
        f n
          <
        M * ((n : ℝ) + 1) ^ 2 :=
      lt_of_not_ge
        hNot

    have hCube :
        (f n) ^ 3
          <
        (
          M * ((n : ℝ) + 1) ^ 2
        ) ^ 3 :=
      pow_lt_pow_left₀
        hfLt
        hfn
        (by norm_num)

    have hBCube :
        B * (f n) ^ 3
          <
        B
          *
        (
          M * ((n : ℝ) + 1) ^ 2
        ) ^ 3 :=
      mul_lt_mul_of_pos_left
        hCube
        hBPos

    have hNLtSuccSq :
        (n : ℝ)
          ≤
        ((n : ℝ) + 1) ^ 2 := by
      nlinarith
        [sq_nonneg (n : ℝ)]

    have hBM3LtSuccSq :
        B * M ^ 3
          <
        ((n : ℝ) + 1) ^ 2 :=
      lt_of_lt_of_le
        hBM3LtN
        hNLtSuccSq

    have hSuccSixPos :
        0 < ((n : ℝ) + 1) ^ 6 := by
      positivity

    have hUpperRaw :
        (B * M ^ 3)
            *
          ((n : ℝ) + 1) ^ 6
          <
        ((n : ℝ) + 1) ^ 2
            *
          ((n : ℝ) + 1) ^ 6 :=
      mul_lt_mul_of_pos_right
        hBM3LtSuccSq
        hSuccSixPos

    have hUpper :
        B
            *
          (
            M * ((n : ℝ) + 1) ^ 2
          ) ^ 3
          <
        ((n : ℝ) + 1) ^ 8 := by

      calc
        B
            *
          (
            M * ((n : ℝ) + 1) ^ 2
          ) ^ 3
            =
          (B * M ^ 3)
            *
          ((n : ℝ) + 1) ^ 6 := by
            ring

        _ <
          ((n : ℝ) + 1) ^ 2
            *
          ((n : ℝ) + 1) ^ 6 :=
          hUpperRaw

        _ =
          ((n : ℝ) + 1) ^ 8 := by
            ring

    have hContradiction :
        B * (f n) ^ 3
          <
        ((n : ℝ) + 1) ^ 8 :=
      lt_trans
        hBCube
        hUpper

    exact
      (not_lt_of_ge hRateN)
        hContradiction

/-! ## Apply the lemma to the synchronized H³ cascade -/

/--
Under hypothetical nonextension there is one localized positive-derivative
sequence on which

* the canonical energy has its explicit quadratic indexed lower bound;
* the raw energy derivative tends to `+∞`;
* top H³ dissipation divided by `(n+1)^2` tends to `+∞`;
* adverse H³ transport divided by `(n+1)^2` tends to `+∞`.

Thus the dissipation and adverse-transport components of the synchronized
cascade are superquadratic in the sequence index.
-/
theorem exists_terminal_superquadratic_h3_cascade_of_noH3PathExtension
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
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Dissipation3At u (σ n)
              /
            ((n : ℝ) + 1) ^ 2
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
            ((n : ℝ) + 1) ^ 2
        )
        atTop
        atTop := by

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hDerivativeTendsto,
      hIndexedRates
    ⟩ :=
    exists_terminal_indexed_h3_cascade_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

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

  have hD3Nonneg :
      ∀ᶠ n : ℕ in atTop,
        0 ≤ velocityH3Dissipation3At u (σ n) :=

    Eventually.of_forall
      (
        fun n =>
          velocityH3Dissipation3At_nonneg
            u
            (σ n)
      )

  have hD3Rate :
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 8
          ≤
        B
          *
        velocityH3Dissipation3At u (σ n) ^ 3 := by

    filter_upwards
      [hIndexedRates]
      with n hn

    simpa only [B] using
      hn.1

  have hD3RatioTendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Dissipation3At u (σ n)
              /
            ((n : ℝ) + 1) ^ 2
        )
        atTop
        atTop :=

    tendsto_div_natSucc_sq_atTop_of_eventually_pow_eight_le_const_mul_cube
      hB
      hD3Nonneg
      hD3Rate

  have hNegativeTransportNonneg :
      ∀ᶠ n : ℕ in atTop,
        0
          ≤
        - velocityH3TransportDerivativeAt u (σ n) :=

    Eventually.of_forall
      (
        fun n => by

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
                (hσ n).2.2.1

          have hD :
              0 ≤ velocityH3DissipationAt u (σ n) :=
            velocityH3DissipationAt_nonneg
              u
              (σ n)

          have hBalance :=
            deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
              hH3
              hClass
              (hσ n).1

          linarith
      )

  have hTransportRate :
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 8
          ≤
        B
          *
        (- velocityH3TransportDerivativeAt u (σ n)) ^ 3 := by

    filter_upwards
      [hIndexedRates]
      with n hn

    have hPowNonneg :
        0 ≤ ((n : ℝ) + 1) ^ 8 := by
      positivity

    have hWeak :
        ((n : ℝ) + 1) ^ 8
          ≤
        8 * ((n : ℝ) + 1) ^ 8 := by
      nlinarith

    exact
      le_trans
        hWeak
        (by
          simpa only [B] using hn.2)

  have hTransportRatioTendsto :
      Tendsto
        (
          fun n : ℕ =>
            (
              - velocityH3TransportDerivativeAt u (σ n)
            )
              /
            ((n : ℝ) + 1) ^ 2
        )
        atTop
        atTop :=

    tendsto_div_natSucc_sq_atTop_of_eventually_pow_eight_le_const_mul_cube
      hB
      hNegativeTransportNonneg
      hTransportRate

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hDerivativeTendsto,
      hD3RatioTendsto,
      hTransportRatioTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
