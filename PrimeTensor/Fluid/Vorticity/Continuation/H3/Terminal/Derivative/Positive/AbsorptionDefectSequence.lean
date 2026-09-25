import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.TransportCubicRate

/-!
# Terminal divergence of the H³ dissipation-absorption defect

The retained-dissipation H³ inequality is

    E'(t) + 2 D(t)
      ≤
    K sqrt(E(t)) E(t),

while the exact balance is

    E'(t) + 2 D(t)
      =
    -T_H3(t).

The positive-derivative terminal sequence constructed earlier satisfies

    E'(σ_n) -> +∞.

Therefore, along the same strict preterminal sequence, two natural
dissipation-absorption defects diverge.

The exact PDE defect is

    -T_H3(σ_n) - 2 D(σ_n)
      =
    E'(σ_n)
      -> +∞.

The analytic Riccati defect is

    K sqrt(E(σ_n)) E(σ_n) - 2 D(σ_n),

and the retained-dissipation inequality gives

    E'(σ_n)
      ≤
    K sqrt(E(σ_n)) E(σ_n) - 2 D(σ_n),

so this defect also tends to `+∞`.

Thus hypothetical nonextension does not merely require failure of pointwise
dissipation absorption.  Along a terminal sequence, both the exact nonlinear
transport excess after paying the full `2D` dissipation and its canonical
sqrt-energy upper envelope exceed that dissipation by an unbounded amount.

This remains a necessary-condition theorem and does not assert existence of a
nonextendible path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Exact balance identifies the signed full-dissipation transport defect with the
raw H³-energy derivative.
-/
theorem negativeTransport_sub_twoDissipation_eq_deriv_velocityH3EnergyAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    - velocityH3TransportDerivativeAt u t
        - 2 * velocityH3DissipationAt u t
      =
    deriv (velocityH3EnergyAt u) t := by

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3
      hClass
      ht

  linarith

/--
The canonical sqrt-energy growth envelope after paying the full `2D`
dissipation dominates the raw H³-energy derivative.
-/
theorem deriv_velocityH3EnergyAt_le_sqrtEnergy_absorptionDefect
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t
      ≤
    h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t)
        *
      velocityH3EnergyAt u t
        -
      2 * velocityH3DissipationAt u t := by

  have hGrowth :=
    deriv_velocityH3EnergyAt_add_two_dissipation_le_sqrtEnergy_mul_energy
      hH3
      hClass
      ht

  linarith

/--
Under hypothetical nonextension, one strict preterminal sequence approaching
`T` simultaneously has

* raw H³-energy derivative tending to `+∞`;
* exact signed transport-after-full-dissipation defect tending to `+∞`;
* canonical sqrt-energy-envelope-after-full-dissipation defect tending to
  `+∞`.
-/
theorem exists_terminal_h3_absorptionDefect_blowupSequence_of_noH3PathExtension
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
            - velocityH3TransportDerivativeAt u (σ n)
              - 2 * velocityH3DissipationAt u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            h3PathSqrtEnergyRiccatiCoefficient
                *
              Real.sqrt (velocityH3EnergyAt u (σ n))
                *
              velocityH3EnergyAt u (σ n)
                -
              2 * velocityH3DissipationAt u (σ n)
        )
        atTop
        atTop := by

  obtain
    ⟨σ, hσ, hSigmaTendsto, hDerivativeTendsto⟩ :=
    exists_deriv_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hActualEventuallyEq :
      (
        fun n : ℕ =>
          - velocityH3TransportDerivativeAt u (σ n)
            - 2 * velocityH3DissipationAt u (σ n)
      )
        =ᶠ[atTop]
      (
        fun n : ℕ =>
          deriv (velocityH3EnergyAt u) (σ n)
      ) := by

    filter_upwards [] with n

    exact
      negativeTransport_sub_twoDissipation_eq_deriv_velocityH3EnergyAt
        hH3
        hClass
        (hσ n).1

  have hActualTendsto :
      Tendsto
        (
          fun n : ℕ =>
            - velocityH3TransportDerivativeAt u (σ n)
              - 2 * velocityH3DissipationAt u (σ n)
        )
        atTop
        atTop :=
    hDerivativeTendsto.congr'
      hActualEventuallyEq.symm

  have hAnalyticTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3PathSqrtEnergyRiccatiCoefficient
                *
              Real.sqrt (velocityH3EnergyAt u (σ n))
                *
              velocityH3EnergyAt u (σ n)
                -
              2 * velocityH3DissipationAt u (σ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hDerivativeEventually :
        ∀ᶠ n : ℕ in atTop,
          M
            ≤
          deriv (velocityH3EnergyAt u) (σ n) :=
      hDerivativeTendsto.eventually
        (eventually_ge_atTop M)

    filter_upwards
      [hDerivativeEventually]
      with n hn

    have hDom :
        deriv (velocityH3EnergyAt u) (σ n)
          ≤
        h3PathSqrtEnergyRiccatiCoefficient
            *
          Real.sqrt (velocityH3EnergyAt u (σ n))
            *
          velocityH3EnergyAt u (σ n)
            -
          2 * velocityH3DissipationAt u (σ n) :=
      deriv_velocityH3EnergyAt_le_sqrtEnergy_absorptionDefect
        hH3
        hClass
        (hσ n).1

    exact
      le_trans
        hn
        hDom

  exact
    ⟨
      σ,
      (fun n => (hσ n).1),
      hSigmaTendsto,
      hDerivativeTendsto,
      hActualTendsto,
      hAnalyticTendsto
    ⟩

/--
Equivalent quantified neighborhood form for the canonical analytic absorption
defect: it is arbitrarily large arbitrarily near `T`.
-/
theorem sqrtEnergy_absorptionDefect_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ ε : ℝ,
      0 < ε →
      ∀ M : ℝ,
        ∃ t : ℝ,
          t ∈ Set.Ioo (T - ε) T
            ∧
          t ∈ Set.Ioo a T
            ∧
          M
            <
          h3PathSqrtEnergyRiccatiCoefficient
              *
            Real.sqrt (velocityH3EnergyAt u t)
              *
            velocityH3EnergyAt u t
              -
            2 * velocityH3DissipationAt u t := by

  intro ε hε M

  obtain
    ⟨t, htNear, htClass, hDerivativeLarge⟩ :=
    deriv_velocityH3EnergyAt_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      ε
      hε
      M

  have hDom :=
    deriv_velocityH3EnergyAt_le_sqrtEnergy_absorptionDefect
      hH3
      hClass
      htClass

  exact
    ⟨
      t,
      htNear,
      htClass,
      lt_of_lt_of_le
        hDerivativeLarge
        hDom
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
