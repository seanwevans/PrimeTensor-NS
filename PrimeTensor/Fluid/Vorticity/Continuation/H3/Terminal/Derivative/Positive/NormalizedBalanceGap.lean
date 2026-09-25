import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.NonnegativeGrowthNormalizedTransport

/-!
# Full-tail normalized H³ balance-gap divergence

The exact H³ balance is

    E'(t) + 2 D(t) = -T_H3(t).

Hence, at every strict H³ energy-class time,

    (-T_H3(t) - E'(t)) / E(t)
      =
    2 * D(t) / E(t).

The full-energy normalized cascade already proves that hypothetical
nonextension forces

    D(t) / E(t) -> +∞    as t ↑ T.

Therefore the exact normalized balance gap

    G(t) :=
      (-T_H3(t) - E'(t)) / E(t)

satisfies

    G(t) -> +∞    as t ↑ T.

This is a full-tail statement with no sign split.  It is algebraically
equivalent to the divergence of normalized full dissipation and remains
completely neutral about whether the large gap is realized by adverse
transport, rapid energy decay, or a mixture of both.

A positive continuation contrapositive is also recorded: if one finite upper
bound for this normalized balance gap recurs arbitrarily late, then smooth
continuation across `T` exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Exact normalized balance identity -/

/--
At every strict H³ energy-class time, the normalized gap between adverse
transport and the H³ energy derivative is exactly twice normalized full
dissipation.
-/
theorem normalized_negativeTransport_sub_deriv_eq_two_mul_dissipation_div_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    (
      (
        - velocityH3TransportDerivativeAt u t
      )
        -
      deriv (velocityH3EnergyAt u) t
    )
      /
    velocityH3EnergyAt u t
      =
    2
      *
    (
      velocityH3DissipationAt u t
        /
      velocityH3EnergyAt u t
    ) := by

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3
      hClass
      ht

  rw [← hBalance]

  ring

/-! ## Full left-terminal divergence -/

/--
Under hypothetical nonextension, the normalized exact-balance gap tends to
`+∞` throughout the entire left terminal neighborhood.
-/
theorem normalized_negativeTransport_sub_deriv_div_energy_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (
        fun t : ℝ =>
          (
            (
              - velocityH3TransportDerivativeAt u t
            )
              -
            deriv (velocityH3EnergyAt u) t
          )
            /
          velocityH3EnergyAt u t
      )
      (𝓝[<] T)
      atTop := by

  have hRatio :=
    velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hTwice :
      Tendsto
        (
          fun t : ℝ =>
            2
              *
            (
              velocityH3DissipationAt u t
                /
              velocityH3EnergyAt u t
            )
        )
        (𝓝[<] T)
        atTop :=
    Tendsto.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)
      hRatio

  have hClassTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT
      hClass.terminal_start.2

  have hEq :
      (
        fun t : ℝ =>
          (
            (
              - velocityH3TransportDerivativeAt u t
            )
              -
            deriv (velocityH3EnergyAt u) t
          )
            /
          velocityH3EnergyAt u t
      )
        =ᶠ[𝓝[<] T]
      (
        fun t : ℝ =>
          2
            *
          (
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
          )
      ) := by

    filter_upwards
      [hClassTail]
      with t ht

    exact
      normalized_negativeTransport_sub_deriv_eq_two_mul_dissipation_div_energy
        hH3
        hClass
        ht

  exact
    Tendsto.congr'
      hEq.symm
      hTwice

/-! ## Explicit strict-tail threshold form -/

/--
For every finite threshold `M`, hypothetical nonextension forces the normalized
balance gap to exceed `M` throughout some strict terminal tail.
-/
theorem exists_terminalTail_normalized_balanceGap_ge_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo a T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        M
          ≤
        (
          (
            - velocityH3TransportDerivativeAt u t
          )
            -
          deriv (velocityH3EnergyAt u) t
        )
          /
        velocityH3EnergyAt u t := by

  have hGap :=
    normalized_negativeTransport_sub_deriv_div_energy_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hEventually :
      {t : ℝ |
        M
          ≤
        (
          (
            - velocityH3TransportDerivativeAt u t
          )
            -
          deriv (velocityH3EnergyAt u) t
        )
          /
        velocityH3EnergyAt u t}
        ∈
      𝓝[<] T :=
    hGap.eventually
      (eventually_ge_atTop M)

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

  intro t ht

  apply
    hdSubset

  constructor

  · exact
      lt_of_le_of_lt
        (le_max_left d b)
        ht.1

  · exact
      ht.2

/-! ## Neutral package -/

/--
Neutral formulation: either smooth continuation exists, or the normalized
exact-balance gap tends to `+∞` along the entire left terminal neighborhood.
-/
theorem smoothContinuationExtension_or_normalized_balanceGap_tendsto_atTop
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
    Tendsto
      (
        fun t : ℝ =>
          (
            (
              - velocityH3TransportDerivativeAt u t
            )
              -
            deriv (velocityH3EnergyAt u) t
          )
            /
          velocityH3EnergyAt u t
      )
      (𝓝[<] T)
      atTop := by

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
          normalized_negativeTransport_sub_deriv_div_energy_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

/-! ## Positive continuation contrapositive -/

/--
If one finite upper bound for the normalized exact-balance gap recurs
arbitrarily late, then smooth continuation across `T` exists.
-/
theorem exists_smoothContinuationExtension_of_normalized_balanceGap_bounded_arbitrarilyLate
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
          (
            (
              - velocityH3TransportDerivativeAt u t
            )
              -
            deriv (velocityH3EnergyAt u) t
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
    exists_terminalTail_normalized_balanceGap_ge_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  obtain
    ⟨t, ht, hUpper⟩ :=
    hRecurring
      c
      hc

  have hLower :=
    hForced
      t
      ht

  exact
    (not_lt_of_ge hLower)
      hUpper

end

end Euclidean
end Bridge
end PrimeTensor
