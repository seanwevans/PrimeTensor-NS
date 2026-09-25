import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.NormalizedBalanceDichotomy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.TopFrequencyCascade

/-!
# Selected positive-growth full-energy transport cascade

The full-tail normalized cascade proves, under hypothetical nonextension,

    E(t) -> +∞,
    D(t) / E(t) -> +∞

as `t ↑ T`.

Independently, the selected positive-derivative cascade supplies one localized
sequence `σ n -> T` with

    n < E'(σ n).

Because every selected time lies strictly below `T`, this sequence converges
to `T` through the left terminal neighborhood.  Hence all full-tail normalized
limits may be composed with the same sequence.

At the selected times the exact balance

    E'(t) + 2 D(t) = -T_H3(t)

and positivity of `E'(σ n)` imply

    D(σ n) ≤ -T_H3(σ n).

Therefore the already-diverging full ratio `D/E` transfers directly to the
adverse transport ratio:

    (-T_H3(σ n)) / E(σ n) -> +∞.

This gives a definite adverse-transport channel on one positive-growth
terminal sequence, while preserving the neutral full-tail balance dichotomy
away from that sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Hypothetical nonextension admits one localized positive-growth terminal
sequence carrying the full-energy cascade

    E -> +∞,
    D / E -> +∞,
    (-T_H3) / E -> +∞.
-/
theorem exists_terminal_fullEnergyTransportCascade_of_noH3PathExtension
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
            (
              - velocityH3TransportDerivativeAt u (σ n)
            )
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
      _hE3Tendsto,
      _hD3RatioTendsto,
      _hFullRatioE3Tendsto,
      _hTransportRatioE3Tendsto
    ⟩ :=
    exists_terminal_topFrequencyCascade_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hSigmaLT :
      Tendsto
        σ
        atTop
        (𝓝[<] T) := by

    refine
      tendsto_nhdsWithin_iff.mpr
        ?_

    constructor

    · exact
        hSigmaTendsto

    · exact
        Eventually.of_forall
          (
            fun n =>
              (hσ n).1.2
          )

  have hEnergyTendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3EnergyAt u (σ n)
        )
        atTop
        atTop :=
    (
      velocityH3EnergyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    ).comp
      hSigmaLT

  have hDissRatioTendsto :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3DissipationAt u (σ n)
              /
            velocityH3EnergyAt u (σ n)
        )
        atTop
        atTop :=
    (
      velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    ).comp
      hSigmaLT

  have hTransportRatioTendsto :
      Tendsto
        (
          fun n : ℕ =>
            (
              - velocityH3TransportDerivativeAt u (σ n)
            )
              /
            velocityH3EnergyAt u (σ n)
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
      [
        hDissEventually
      ]
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

    have hBalance :=
      deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
        hH3
        hClass
        hClassN

    have hDissNonneg :
        0 ≤ velocityH3DissipationAt u (σ n) :=
      velocityH3DissipationAt_nonneg
        u
        (σ n)

    have hTransportDom :
        velocityH3DissipationAt u (σ n)
          ≤
        - velocityH3TransportDerivativeAt u (σ n) := by

      linarith

    have hEnergyNonneg :
        0 ≤ velocityH3EnergyAt u (σ n) := by

      have hOne :=
        one_le_velocityH3EnergyAt
          u
          (σ n)

      linarith

    have hRatio :
        velocityH3DissipationAt u (σ n)
            /
          velocityH3EnergyAt u (σ n)
          ≤
        (
          - velocityH3TransportDerivativeAt u (σ n)
        )
            /
          velocityH3EnergyAt u (σ n) :=
      div_le_div_of_nonneg_right
        hTransportDom
        hEnergyNonneg

    exact
      le_trans
        hn
        hRatio

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      hTransportRatioTendsto
    ⟩

/--
Equivalent neutral formulation: either smooth continuation exists, or there is
one positive-growth terminal sequence on which the full energy, normalized
dissipation, and normalized adverse transport all diverge as stated above.
-/
theorem smoothContinuationExtension_or_terminal_fullEnergyTransportCascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
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
              (
                - velocityH3TransportDerivativeAt u (σ n)
              )
                /
              velocityH3EnergyAt u (σ n)
          )
          atTop
          atTop
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          exists_terminal_fullEnergyTransportCascade_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
