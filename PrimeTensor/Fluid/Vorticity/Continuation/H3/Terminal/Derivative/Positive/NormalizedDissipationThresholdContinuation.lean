import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.NormalizedDissipationRate

/-!
# Quantitative normalized H³ threshold continuation criteria

Let

    A_b =
      3 K² (E₀(b)+1) (4+3E₀(b))³.

The quantitative normalized dissipation theorem proves that hypothetical
nonextension forces, eventually,

    1 ≤ A_b (T-t)² (D(t)/E(t))³.

Thus smooth continuation follows if the complementary strict inequality

    A_b (T-t)² (D(t)/E(t))³ < 1

occurs arbitrarily late.

For the exact normalized balance gap

    G(t) = (-T_H3(t)-E'(t))/E(t) = 2D(t)/E(t),

hypothetical nonextension forces

    8 ≤ A_b (T-t)² G(t)³.

Hence an arbitrarily-late strict violation of that factor-eight threshold also
forces continuation.

These are contrapositives of necessary conditions on hypothetical
nonextension; they do not select a singular or continuation branch a priori.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Strict-tail balance-gap rate -/

/--
Strict-tail form of the quantitative normalized balance-gap rate.
-/
theorem exists_terminalTail_normalized_balanceGap_cubic_rate_of_noH3PathExtension
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
        8
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
        (
          (
            (
              - velocityH3TransportDerivativeAt u t
            )
              -
            deriv (velocityH3EnergyAt u) t
          )
            /
          velocityH3EnergyAt u t
        ) ^ 3 := by

  have hEventually :=
    eventually_normalized_balanceGap_cubic_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  obtain
    ⟨d, hdT, hdSubset⟩ :=
    (
      mem_nhdsLT_iff_exists_Ioo_subset
    ).1
      hEventually

  let c : ℝ :=
    (max d b + T) / 2

  have hMaxT :
      max d b < T :=
    max_lt
      hdT
      hb.2

  have hMaxC :
      max d b < c := by

    dsimp only [c]

    linarith

  have hcT :
      c < T := by

    dsimp only [c]

    linarith

  have hc :
      c ∈ Set.Ioo b T := by

    constructor

    · exact
        lt_of_le_of_lt
          (le_max_right d b)
          hMaxC

    · exact
        hcT

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
      lt_trans
        (
          lt_of_le_of_lt
            (le_max_left d b)
            hMaxC
        )
        ht.1

  · exact
      ht.2

/-! ## Normalized dissipation threshold continuation -/

/--
If the quantitative normalized full-dissipation obstruction is strictly
subcritical at arbitrarily late times, then the H³ path extends smoothly
across `T`.
-/
theorem exists_smoothContinuationExtension_of_normalized_dissipation_cubic_subcritical_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hSubcritical :
      ∀ c : ℝ,
        c ∈ Set.Ioo b T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
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
            (
              velocityH3DissipationAt u t
                /
              velocityH3EnergyAt u t
            ) ^ 3
              <
            1) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  obtain
    ⟨c, hc, hForced⟩ :=
    exists_terminalTail_normalized_dissipation_cubic_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  obtain
    ⟨t, ht, hBelow⟩ :=
    hSubcritical
      c
      hc

  have hAbove :=
    hForced
      t
      ht

  exact
    (not_lt_of_ge hAbove)
      hBelow

/-! ## Normalized balance-gap threshold continuation -/

/--
If the exact normalized balance gap violates its forced factor-eight cubic
threshold at arbitrarily late times, then smooth continuation exists.
-/
theorem exists_smoothContinuationExtension_of_normalized_balanceGap_cubic_subcritical_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hSubcritical :
      ∀ c : ℝ,
        c ∈ Set.Ioo b T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
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
            (
              (
                (
                  - velocityH3TransportDerivativeAt u t
                )
                  -
                deriv (velocityH3EnergyAt u) t
              )
                /
              velocityH3EnergyAt u t
            ) ^ 3
              <
            8) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  obtain
    ⟨c, hc, hForced⟩ :=
    exists_terminalTail_normalized_balanceGap_cubic_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  obtain
    ⟨t, ht, hBelow⟩ :=
    hSubcritical
      c
      hc

  have hAbove :=
    hForced
      t
      ht

  exact
    (not_lt_of_ge hAbove)
      hBelow

/-! ## Neutral threshold dichotomies -/

/--
Neutral quantitative full-dissipation dichotomy.

Either smooth continuation exists, or the normalized full-dissipation cubic
threshold is eventually forced.
-/
theorem smoothContinuationExtension_or_eventual_normalized_dissipation_cubic_rate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∀ᶠ t : ℝ in 𝓝[<] T,
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
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        ) ^ 3
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
          eventually_normalized_dissipation_cubic_rate_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

/--
Neutral quantitative exact-balance-gap dichotomy.

Either smooth continuation exists, or the factor-eight normalized balance-gap
cubic threshold is eventually forced.
-/
theorem smoothContinuationExtension_or_eventual_normalized_balanceGap_cubic_rate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∀ᶠ t : ℝ in 𝓝[<] T,
        8
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
        (
          (
            (
              - velocityH3TransportDerivativeAt u t
            )
              -
            deriv (velocityH3EnergyAt u) t
          )
            /
          velocityH3EnergyAt u t
        ) ^ 3
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
          eventually_normalized_balanceGap_cubic_rate_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

/-! ## Canonical midpoint specializations -/

/--
Canonical midpoint-anchor normalized dissipation threshold criterion.
-/
theorem exists_smoothContinuationExtension_of_normalized_dissipation_cubic_subcritical_arbitrarilyLate_midpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hSubcritical :
      ∀ c : ℝ,
        c ∈
          Set.Ioo
            (h3BKMKineticTailMidpoint a T)
            T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          3
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
            (
              velocityH3Energy0At
                u
                (h3BKMKineticTailMidpoint a T)
                +
              1
            )
              *
            (
              4
                +
              3
                *
              velocityH3Energy0At
                u
                (h3BKMKineticTailMidpoint a T)
            ) ^ 3
              *
            (T - t) ^ 2
              *
            (
              velocityH3DissipationAt u t
                /
              velocityH3EnergyAt u t
            ) ^ 3
              <
            1) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    exists_smoothContinuationExtension_of_normalized_dissipation_cubic_subcritical_arbitrarilyLate
      hH3
      hClass
      (
        h3BKMKineticTailMidpoint_mem_Ioo
          hClass.terminal_start.2
      )
      hSubcritical

/--
Canonical midpoint-anchor normalized balance-gap threshold criterion.
-/
theorem exists_smoothContinuationExtension_of_normalized_balanceGap_cubic_subcritical_arbitrarilyLate_midpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hSubcritical :
      ∀ c : ℝ,
        c ∈
          Set.Ioo
            (h3BKMKineticTailMidpoint a T)
            T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          3
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 2
              *
            (
              velocityH3Energy0At
                u
                (h3BKMKineticTailMidpoint a T)
                +
              1
            )
              *
            (
              4
                +
              3
                *
              velocityH3Energy0At
                u
                (h3BKMKineticTailMidpoint a T)
            ) ^ 3
              *
            (T - t) ^ 2
              *
            (
              (
                (
                  - velocityH3TransportDerivativeAt u t
                )
                  -
                deriv (velocityH3EnergyAt u) t
              )
                /
              velocityH3EnergyAt u t
            ) ^ 3
              <
            8) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    exists_smoothContinuationExtension_of_normalized_balanceGap_cubic_subcritical_arbitrarilyLate
      hH3
      hClass
      (
        h3BKMKineticTailMidpoint_mem_Ioo
          hClass.terminal_start.2
      )
      hSubcritical

end

end Euclidean
end Bridge
end PrimeTensor
