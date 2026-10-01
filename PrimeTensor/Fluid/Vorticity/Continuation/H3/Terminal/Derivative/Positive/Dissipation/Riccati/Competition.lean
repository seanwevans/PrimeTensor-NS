import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Dissipative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Full.Energy.Transport.Sequence

/-!
# Positive-growth dissipation competition at the H³ terminal frontier

The retained-dissipation Riccati estimate is

    E'(t) + 2 D(t)
      ≤
    K sqrt(E(t)) E(t),

where

    K = h3PathSqrtEnergyRiccatiCoefficient.

At any strict H³ energy-class time with nonnegative energy growth this forces

    2 D(t) / E(t)
      ≤
    K sqrt(E(t)).

At a strictly positive-growth time the inequality is strict.

Thus positive H³ growth can occur only while normalized viscous dissipation
remains below the square-root-energy Riccati envelope.  Equivalently, if

    K sqrt(E(t)) E(t) ≤ 2 D(t),

then the H³ energy cannot increase at that time.

Under hypothetical nonextension the canonical positive-growth terminal
sequence has

    E'(σ_n) > n,

so every selected time lies strictly inside the nonabsorbed regime

    2 D(σ_n) / E(σ_n)
      <
    K sqrt(E(σ_n)).

The same sequence already carries

    E(σ_n) -> +∞,
    D(σ_n) / E(σ_n) -> +∞.

This is a necessary competition law on the nonextension branch.  It does not
assert that such a branch exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pointwise normalized competition -/

/--
At a nonnegative-growth time, normalized full H³ dissipation is at most half
the Riccati square-root-energy envelope, in division-free factor-two form.
-/
theorem two_mul_dissipation_div_energy_le_riccati_mul_sqrtEnergy_of_nonnegative_deriv
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDerivative :
      0 ≤ deriv (velocityH3EnergyAt u) t) :
    2
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      )
      ≤
    h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) := by

  have hGrowth :=
    deriv_velocityH3EnergyAt_add_two_dissipation_le_sqrtEnergy_mul_energy
      hH3
      hClass
      ht

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hScaled :
      2 * velocityH3DissipationAt u t
        ≤
      (
        h3PathSqrtEnergyRiccatiCoefficient
          *
        Real.sqrt (velocityH3EnergyAt u t)
      )
        *
      velocityH3EnergyAt u t := by
    linarith

  calc
    2
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      )
        =
      (
        2 * velocityH3DissipationAt u t
      )
        /
      velocityH3EnergyAt u t := by
      ring

    _ ≤
      h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) :=
      (div_le_iff₀ hEPos).2
        hScaled

/--
At a strictly positive-growth time the normalized dissipation competition is
strict.
-/
theorem two_mul_dissipation_div_energy_lt_riccati_mul_sqrtEnergy_of_pos_deriv
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDerivative :
      0 < deriv (velocityH3EnergyAt u) t) :
    2
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      )
      <
    h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) := by

  have hGrowth :=
    deriv_velocityH3EnergyAt_add_two_dissipation_le_sqrtEnergy_mul_energy
      hH3
      hClass
      ht

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hScaled :
      2 * velocityH3DissipationAt u t
        <
      (
        h3PathSqrtEnergyRiccatiCoefficient
          *
        Real.sqrt (velocityH3EnergyAt u t)
      )
        *
      velocityH3EnergyAt u t := by
    linarith

  calc
    2
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      )
        =
      (
        2 * velocityH3DissipationAt u t
      )
        /
      velocityH3EnergyAt u t := by
      ring

    _ <
      h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) :=
      (div_lt_iff₀ hEPos).2
        hScaled

/-! ## Equivalent absorption criterion -/

/--
If the Riccati growth envelope is absorbed by twice the full H³ dissipation,
then the H³ energy derivative is nonpositive.
-/
theorem deriv_velocityH3EnergyAt_nonpos_of_normalized_dissipation_ge_riccati_sqrtEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAbsorb :
      h3PathSqrtEnergyRiccatiCoefficient
          *
        Real.sqrt (velocityH3EnergyAt u t)
        ≤
      2
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      )) :
    deriv (velocityH3EnergyAt u) t ≤ 0 := by

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hScaled :=
    mul_le_mul_of_nonneg_right
      hAbsorb
      (le_of_lt hEPos)

  have hNormalize :
      (
        2
          *
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        )
      )
        *
      velocityH3EnergyAt u t
        =
      2 * velocityH3DissipationAt u t := by
    field_simp [ne_of_gt hEPos]
    <;> ring

  rw [hNormalize] at hScaled

  exact
    deriv_velocityH3EnergyAt_nonpos_of_dissipation_absorbs_sqrtEnergy
      hH3
      hClass
      ht
      hScaled

/-! ## Terminal sequence form -/

/--
Hypothetical nonextension admits one localized positive-growth terminal
sequence on which

* the H³ energy tends to `+∞`;
* normalized full dissipation tends to `+∞`;
* nevertheless normalized dissipation remains strictly below the Riccati
  square-root-energy envelope at every selected time.
-/
theorem exists_terminal_positiveGrowth_dissipationBelowRiccatiEnvelope_sequence_of_noH3PathExtension
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
          2
              *
            (
              velocityH3DissipationAt u (σ n)
                /
              velocityH3EnergyAt u (σ n)
            )
            <
          h3PathSqrtEnergyRiccatiCoefficient
              *
            Real.sqrt
              (velocityH3EnergyAt u (σ n))
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

  have hCompetition :
      ∀ n : ℕ,
        2
            *
          (
            velocityH3DissipationAt u (σ n)
              /
            velocityH3EnergyAt u (σ n)
          )
          <
        h3PathSqrtEnergyRiccatiCoefficient
            *
          Real.sqrt
            (velocityH3EnergyAt u (σ n)) := by

    intro n

    have hDerivativePos :
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

    exact
      two_mul_dissipation_div_energy_lt_riccati_mul_sqrtEnergy_of_pos_deriv
        hH3
        hClass
        (hσ n).1
        hDerivativePos

  exact
    ⟨
      σ,
      (
        fun n =>
          ⟨
            (hσ n).1,
            (hσ n).2.1,
            (hσ n).2.2,
            hCompetition n
          ⟩
      ),
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto
    ⟩

/-! ## Arbitrarily-late form -/

/--
On a hypothetical nonextension branch, the nonabsorbed regime recurs
arbitrarily late: every strict terminal subtail contains a time where

    2 D/E < K sqrt(E).
-/
theorem exists_arbitrarilyLate_dissipationBelowRiccatiEnvelope_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ b : ℝ,
      b ∈ Set.Ioo a T →
      ∃ t : ℝ,
        t ∈ Set.Ioo b T
          ∧
        2
            *
          (
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
          )
          <
        h3PathSqrtEnergyRiccatiCoefficient
            *
          Real.sqrt
            (velocityH3EnergyAt u t) := by

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      _hEnergyTendsto,
      _hDissRatioTendsto
    ⟩ :=
    exists_terminal_positiveGrowth_dissipationBelowRiccatiEnvelope_sequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  intro b hb

  have hEventuallyAbove :
      ∀ᶠ n : ℕ in atTop,
        b < σ n :=
    (tendsto_order.1 hSigmaTendsto).1
      b
      hb.2

  obtain
    ⟨n, hbn⟩ :=
    hEventuallyAbove.exists

  exact
    ⟨
      σ n,
      ⟨
        hbn,
        (hσ n).1.2
      ⟩,
      (hσ n).2.2.2
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
