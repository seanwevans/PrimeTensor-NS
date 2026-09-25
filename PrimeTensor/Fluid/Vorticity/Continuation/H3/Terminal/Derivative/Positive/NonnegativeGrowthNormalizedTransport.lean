import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.FullEnergyTransportSequence

/-!
# Normalized adverse transport on the late nondecreasing-energy set

The full-energy normalized cascade proves that hypothetical nonextension forces

    D(t) / E(t) -> +∞    as t ↑ T.

At any strict H³ energy-class time with nonnegative energy derivative, the
exact balance

    E'(t) + 2 D(t) = -T_H3(t)

implies

    D(t) ≤ -T_H3(t).

Hence every fixed lower threshold carried by `D/E` transfers to normalized
adverse transport at every sufficiently late time for which `E'(t) ≥ 0`.

Consequently, under hypothetical nonextension, for every finite `M`,

    E'(t) ≥ 0
      ->
    M ≤ (-T_H3(t)) / E(t)

throughout some sufficiently late terminal tail.

This is stronger than a statement along one selected sequence, but it does not
claim transport dominance at late times where the H³ energy is decreasing.

A positive continuation contrapositive is also recorded: if one finite
normalized transport cap recurs arbitrarily late at nonnegative-growth times,
then smooth continuation across `T` exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pointwise normalized transport transfer -/

/--
At a strict H³ energy-class time with nonnegative energy derivative, normalized
full dissipation is bounded above by normalized adverse transport.
-/
theorem dissipation_div_energy_le_negativeTransport_div_energy_of_nonnegative_deriv
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
    (
      - velocityH3TransportDerivativeAt u t
    )
        /
      velocityH3EnergyAt u t := by

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3
      hClass
      ht

  have hDissNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg
      u t

  have hTransportDom :
      velocityH3DissipationAt u t
        ≤
      - velocityH3TransportDerivativeAt u t := by

    linarith

  have hEnergyNonneg :
      0 ≤ velocityH3EnergyAt u t := by

    have hOne :=
      one_le_velocityH3EnergyAt
        u t

    linarith

  exact
    div_le_div_of_nonneg_right
      hTransportDom
      hEnergyNonneg

/-! ## Full late-time implication under nonextension -/

/--
Under hypothetical nonextension, every finite normalized transport threshold is
eventually forced at every time of nonnegative H³-energy growth.
-/
theorem eventually_nonnegative_deriv_implies_normalized_negativeTransport_ge_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (M : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      0 ≤ deriv (velocityH3EnergyAt u) t →
      M
        ≤
      (
        - velocityH3TransportDerivativeAt u t
      )
        /
      velocityH3EnergyAt u t := by

  have hRatio :=
    velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hLower :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M
          ≤
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t :=
    hRatio.eventually
      (eventually_ge_atTop M)

  have hClassTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT
      hClass.terminal_start.2

  filter_upwards
    [
      hLower,
      hClassTail
    ]
    with t hLowerT ht

  intro hDerivative

  have hTransfer :=
    dissipation_div_energy_le_negativeTransport_div_energy_of_nonnegative_deriv
      hH3
      hClass
      ht
      hDerivative

  exact
    le_trans
      hLowerT
      hTransfer

/-! ## Explicit strict-tail form -/

/--
Strict-tail version: for every finite `M`, hypothetical nonextension supplies a
strict terminal time after which every nonnegative-growth time has normalized
adverse transport at least `M`.
-/
theorem exists_terminalTail_nonnegative_deriv_implies_normalized_negativeTransport_ge_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (M : ℝ) :
    ∃ c : ℝ,
      c ∈ Set.Ioo a T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        0 ≤ deriv (velocityH3EnergyAt u) t →
        M
          ≤
        (
          - velocityH3TransportDerivativeAt u t
        )
          /
        velocityH3EnergyAt u t := by

  have hEventually :=
    eventually_nonnegative_deriv_implies_normalized_negativeTransport_ge_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      M

  obtain
    ⟨d, hdT, hdSubset⟩ :=
    (
      mem_nhdsLT_iff_exists_Ioo_subset
    ).1
      hEventually

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  let c : ℝ :=
    max d b

  have hc :
      c ∈ Set.Ioo a T := by

    constructor

    · dsimp only [c]

      exact
        lt_of_lt_of_le
          hb.1
          (le_max_right _ _)

    · dsimp only [c]

      exact
        max_lt
          hdT
          hb.2

  refine
    ⟨
      c,
      hc,
      ?_
    ⟩

  intro t ht hDerivative

  apply
    hdSubset

  · constructor

    · exact
        lt_of_le_of_lt
          (le_max_left d b)
          ht.1

    · exact
        ht.2

  · exact
      hDerivative

/-! ## Neutral terminal package -/

/--
Neutral formulation: either smooth continuation exists, or every finite
normalized adverse-transport threshold is eventually forced at all
nonnegative-growth times.
-/
theorem smoothContinuationExtension_or_eventually_nonnegativeGrowth_normalizedTransport
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
      ∀ M : ℝ,
        ∀ᶠ t : ℝ in 𝓝[<] T,
          0 ≤ deriv (velocityH3EnergyAt u) t →
          M
            ≤
          (
            - velocityH3TransportDerivativeAt u t
          )
            /
          velocityH3EnergyAt u t
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · right

    intro M

    exact
      eventually_nonnegative_deriv_implies_normalized_negativeTransport_ge_of_noH3PathExtension
        hH3
        hExtension
        hClass
        M

/-! ## Positive continuation contrapositive -/

/--
If one finite normalized adverse-transport cap recurs arbitrarily late at
nonnegative-growth times, then smooth continuation across `T` exists.
-/
theorem exists_smoothContinuationExtension_of_nonnegativeGrowth_normalizedTransport_bounded_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hRecurring :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          0 ≤ deriv (velocityH3EnergyAt u) t
            ∧
          (
            - velocityH3TransportDerivativeAt u t
          )
            /
          velocityH3EnergyAt u t
            <
          M) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  obtain
    ⟨c, hc, hForced⟩ :=
    exists_terminalTail_nonnegative_deriv_implies_normalized_negativeTransport_ge_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      M

  obtain
    ⟨t, ht, hDerivative, hUpper⟩ :=
    hRecurring
      c
      hc

  have hLower :=
    hForced
      t
      ht
      hDerivative

  exact
    (not_lt_of_ge hLower)
      hUpper

end

end Euclidean
end Bridge
end PrimeTensor
