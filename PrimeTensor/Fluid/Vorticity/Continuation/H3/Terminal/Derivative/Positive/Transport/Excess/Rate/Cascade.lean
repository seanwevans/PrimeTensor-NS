import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Excess.Partial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Normalized.Dissipation.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Full.Energy.Transport.Sequence

/-!
# Quantitative terminal obstruction for the minimal one-copy transport excess

The explicit one-copy transport excess is

    q(t) =
      max 0 ((-T_H3(t) - D(t)) / E(t)).

At every strict H³ energy-class time the exact balance is

    E'(t) + 2 D(t) = -T_H3(t).

Hence whenever `E'(t) ≥ 0`,

    -T_H3(t) - D(t)
      =
    E'(t) + D(t)
      ≥
    D(t),

and therefore

    D(t) / E(t) ≤ q(t).

This transfers the previously proved normalized-dissipation obstruction
directly to the explicit minimal nonlinear absorption coefficient.

Under hypothetical nonextension:

* on every sufficiently late terminal tail, at every nonnegative-growth time,

      1 ≤ A_b (T-t)^2 q(t)^3;

* along the canonical positive-growth terminal sequence,

      q(σ_n) → +∞.

Thus the unresolved continuation frontier can be stated directly in terms of
the explicit nonlinear excess rate itself, with no auxiliary majorant and no
loss of the quantitative terminal rate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pointwise domination of normalized dissipation -/

/--
At every strict H³ energy-class time of nonnegative energy growth, the minimal
one-copy transport excess dominates normalized full dissipation.
-/
theorem velocityH3Dissipation_div_energy_le_transportExcessRate_of_nonnegative_deriv
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDerivative :
      0 ≤ deriv (velocityH3EnergyAt u) t) :
    velocityH3DissipationAt u t
        /
      velocityH3EnergyAt u t
      ≤
    h3PathTransportExcessRate u t := by

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3
      hClass
      ht

  have hDNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg
      u t

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt
      u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hENonneg :
      0 ≤ velocityH3EnergyAt u t :=
    le_of_lt hEPos

  have hNumeratorEq :
      - velocityH3TransportDerivativeAt u t
          - velocityH3DissipationAt u t
        =
      deriv (velocityH3EnergyAt u) t
          + velocityH3DissipationAt u t := by
    linarith

  have hNumeratorNonneg :
      0
        ≤
      deriv (velocityH3EnergyAt u) t
        + velocityH3DissipationAt u t :=
    add_nonneg
      hDerivative
      hDNonneg

  have hRatioNonneg :
      0
        ≤
      (
        deriv (velocityH3EnergyAt u) t
          + velocityH3DissipationAt u t
      )
        /
      velocityH3EnergyAt u t :=
    div_nonneg
      hNumeratorNonneg
      hENonneg

  have hDLe :
      velocityH3DissipationAt u t
        ≤
      deriv (velocityH3EnergyAt u) t
        + velocityH3DissipationAt u t := by
    linarith

  have hRatioLe :
      velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
        ≤
      (
        deriv (velocityH3EnergyAt u) t
          + velocityH3DissipationAt u t
      )
        /
      velocityH3EnergyAt u t :=
    div_le_div_of_nonneg_right
      hDLe
      hENonneg

  unfold h3PathTransportExcessRate

  rw [hNumeratorEq]

  rw [max_eq_right hRatioNonneg]

  exact
    hRatioLe

/-! ## Cubic terminal-rate transfer -/

/--
A cubic normalized-dissipation lower rate transfers directly to the minimal
one-copy transport excess at nonnegative-growth times.
-/
theorem one_le_transportExcessRate_cubic_of_normalizedDissipation_cubic_of_nonnegative_deriv
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t A : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hA : 0 ≤ A)
    (hDerivative :
      0 ≤ deriv (velocityH3EnergyAt u) t)
    (hRate :
      1
        ≤
      A
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      ) ^ 3) :
    1
      ≤
    A
      *
    (h3PathTransportExcessRate u t) ^ 3 := by

  have hRatioNonneg :
      0
        ≤
      velocityH3DissipationAt u t
        /
      velocityH3EnergyAt u t := by

    have hEnergyNonneg :
        0 ≤ velocityH3EnergyAt u t := by
      linarith [one_le_velocityH3EnergyAt u t]

    exact
      div_nonneg
        (velocityH3DissipationAt_nonneg
          u t)
        hEnergyNonneg

  have hExcessDom :=
    velocityH3Dissipation_div_energy_le_transportExcessRate_of_nonnegative_deriv
      hH3
      hClass
      ht
      hDerivative

  have hCube :
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      ) ^ 3
        ≤
      (h3PathTransportExcessRate u t) ^ 3 :=
    pow_le_pow_left₀
      hRatioNonneg
      hExcessDom
      3

  have hScaled :
      A
          *
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        ) ^ 3
        ≤
      A
          *
        (h3PathTransportExcessRate u t) ^ 3 :=
    mul_le_mul_of_nonneg_left
      hCube
      hA

  exact
    le_trans
      hRate
      hScaled

/-! ## Full terminal-tail quantitative obstruction -/

/--
Hypothetical nonextension forces the same inverse-`2/3` cubic terminal rate
for the explicit one-copy transport excess at every sufficiently late time
where the H³ energy derivative is nonnegative.
-/
theorem exists_terminalTail_transportExcessRate_cubic_rate_of_nonnegative_deriv_of_noH3PathExtension
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
        0 ≤ deriv (velocityH3EnergyAt u) t →
        1
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
        (
          4
            +
          3 * velocityH3Energy0At u b
        ) ^ 3
          *
        (T - t) ^ 2
          *
        (h3PathTransportExcessRate u t) ^ 3 := by

  obtain
    ⟨
      c,
      hc,
      hDissRate
    ⟩ :=
    exists_terminalTail_normalized_dissipation_cubic_rate_of_noH3PathExtension
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

  intro t ht hDerivative

  have htClass :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans
        hb.1
        (lt_trans hc.1 ht.1),
      ht.2
    ⟩

  let A : ℝ :=
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
    (
      4
        +
      3 * velocityH3Energy0At u b
    ) ^ 3
      *
    (T - t) ^ 2

  have hA :
      0 ≤ A := by

    have hE0 :
        0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg
        u b

    dsimp only [A]

    positivity

  have hRateA :
      1
        ≤
      A
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      ) ^ 3 := by

    dsimp only [A]

    simpa only [mul_assoc] using
      hDissRate
        t
        ht

  have hTransfer :=
    one_le_transportExcessRate_cubic_of_normalizedDissipation_cubic_of_nonnegative_deriv
      hH3
      hClass
      htClass
      hA
      hDerivative
      hRateA

  dsimp only [A] at hTransfer

  exact
    hTransfer

/-! ## Divergence on the canonical positive-growth sequence -/

/--
Under hypothetical nonextension, the explicit minimal one-copy transport excess
tends to `+∞` along the canonical positive-growth full-energy terminal
sequence.
-/
theorem exists_terminal_transportExcessRate_tendsto_atTop_on_positiveGrowthSequence_of_noH3PathExtension
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
            velocityH3EnergyAt u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3DissipationAt u (σ n)
              /
            velocityH3EnergyAt u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            h3PathTransportExcessRate
              u
              (σ n)
        )
        atTop
        atTop := by

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      _hTransportRatioTendsto
    ⟩ :=
    exists_terminal_fullEnergyTransportCascade_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hExcessTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3PathTransportExcessRate
              u
              (σ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hDissEventually :
        ∀ᶠ n : ℕ in atTop,
          M
            ≤
          velocityH3DissipationAt u (σ n)
            /
          velocityH3EnergyAt u (σ n) :=
      hDissRatioTendsto.eventually
        (eventually_ge_atTop M)

    filter_upwards
      [hDissEventually]
      with n hn

    have hDerivativeNonneg :
        0
          ≤
        deriv (velocityH3EnergyAt u) (σ n) := by

      have hnNonneg :
          0 ≤ (n : ℝ) :=
        Nat.cast_nonneg n

      exact
        le_of_lt
          (
            lt_of_le_of_lt
              hnNonneg
              (hσ n).2.2
          )

    have hDom :=
      velocityH3Dissipation_div_energy_le_transportExcessRate_of_nonnegative_deriv
        hH3
        hClass
        (hσ n).1
        hDerivativeNonneg

    exact
      le_trans
        hn
        hDom

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      hExcessTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
