import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.NormalizedBalanceGap
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicFrequencyRate

/-!
# Quantitative full-energy normalized terminal dissipation rate

The top characteristic-frequency rate under hypothetical nonextension is

    1
      ≤
    3 K² (E₀(b)+1) (T-t)² Λ₃(t)^6.

On the same late tail, the full H³ energy satisfies

    E(t) ≤ C_b E₃(t),

with

    C_b = 4 + 3 E₀(b).

Since

    Λ₃(t)^2 = D₃(t) / E₃(t),

the energy comparison implies

    Λ₃(t)^2
      ≤
    C_b * D₃(t) / E(t).

Cubing and inserting the characteristic-frequency rate yields the
division-free full-energy normalized estimate

    1
      ≤
    3 K² (E₀(b)+1) C_b^3
      (T-t)²
      (D₃(t)/E(t))^3.

Because `D₃ ≤ D`, the same estimate holds with `D/E`.

Finally, the exact normalized balance identity

    G(t) = (-T_H3(t) - E'(t)) / E(t) = 2 D(t)/E(t)

gives the sharp balance-gap form

    8
      ≤
    3 K² (E₀(b)+1) C_b^3
      (T-t)²
      G(t)^3.

These are quantitative necessary conditions on a hypothetical nonextension
branch.  They do not assert that such a branch exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Top dissipation normalized by full H³ energy -/

/--
Hypothetical nonextension forces the full-energy normalized top dissipation to
carry an inverse-`2/3` terminal rate in division-free cubic form.
-/
theorem eventually_normalized_dissipation3_cubic_rate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
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
        velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t
      ) ^ 3 := by

  obtain
    ⟨cRate, hcRate, hFrequencyRate⟩ :=
    exists_terminalTail_characteristicFrequency_pow_six_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  have hFrequencyEventually :
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
        (T - t) ^ 2
          *
        h3TopCharacteristicFrequencyAt u t ^ 6 := by

    filter_upwards
      [
        Ioo_mem_nhdsLT hcRate.2
      ]
      with t ht

    exact
      hFrequencyRate
        t
        ht

  have hEnergyUpper :=
    eventually_velocityH3EnergyAt_le_anchorCoefficient_mul_energy3_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  filter_upwards
    [
      hFrequencyEventually,
      hEnergyUpper
    ]
    with t hFrequency hUpper

  let C : ℝ :=
    4
      +
    3 * velocityH3Energy0At u b

  let R : ℝ :=
    velocityH3Dissipation3At u t
      /
    velocityH3EnergyAt u t

  have hE0 :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  have hCPos :
      0 < C := by

    dsimp only [C]

    linarith

  have hCNonneg :
      0 ≤ C :=
    le_of_lt hCPos

  have hEnergyOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt
      u t

  have hEnergyPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hEnergyNonneg :
      0 ≤ velocityH3EnergyAt u t :=
    le_of_lt hEnergyPos

  have hE3Nonneg :
      0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg
      u t

  have hUpperC :
      velocityH3EnergyAt u t
        ≤
      C * velocityH3Energy3At u t := by

    dsimp only [C]

    exact
      hUpper

  have hE3Pos :
      0 < velocityH3Energy3At u t := by

    by_contra hNot

    have hE3Zero :
        velocityH3Energy3At u t = 0 :=
      le_antisymm
        (le_of_not_gt hNot)
        hE3Nonneg

    rw [hE3Zero, mul_zero] at hUpperC

    linarith

  have hD3Nonneg :
      0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg
      u t

  have hRNonneg :
      0 ≤ R := by

    dsimp only [R]

    exact
      div_nonneg
        hD3Nonneg
        hEnergyNonneg

  have hScaledEnergy :
      R * velocityH3EnergyAt u t
        ≤
      R * (C * velocityH3Energy3At u t) :=
    mul_le_mul_of_nonneg_left
      hUpperC
      hRNonneg

  have hD3Le :
      velocityH3Dissipation3At u t
        ≤
      (C * R) * velocityH3Energy3At u t := by

    calc
      velocityH3Dissipation3At u t
          =
        R * velocityH3EnergyAt u t := by

          dsimp only [R]

          field_simp

      _ ≤
        R * (C * velocityH3Energy3At u t) :=
        hScaledEnergy

      _ =
        (C * R) * velocityH3Energy3At u t := by
        ring

  have hIntrinsicRatio :
      velocityH3Dissipation3At u t
          /
        velocityH3Energy3At u t
        ≤
      C * R :=
    (div_le_iff₀ hE3Pos).2
      hD3Le

  have hLambdaSq :
      h3TopCharacteristicFrequencyAt u t ^ 2
        ≤
      C * R := by

    rw [
      h3TopCharacteristicFrequencyAt_sq
    ]

    exact
      hIntrinsicRatio

  have hRightNonneg :
      0 ≤ C * R :=
    mul_nonneg
      hCNonneg
      hRNonneg

  have hCube :
      (
        h3TopCharacteristicFrequencyAt u t ^ 2
      ) ^ 3
        ≤
      (C * R) ^ 3 :=
    pow_le_pow_left₀
      (sq_nonneg
        (h3TopCharacteristicFrequencyAt u t))
      hLambdaSq
      3

  have hSix :
      h3TopCharacteristicFrequencyAt u t ^ 6
        ≤
      C ^ 3 * R ^ 3 := by

    calc
      h3TopCharacteristicFrequencyAt u t ^ 6
          =
        (
          h3TopCharacteristicFrequencyAt u t ^ 2
        ) ^ 3 := by
          ring

      _ ≤
        (C * R) ^ 3 :=
        hCube

      _ =
        C ^ 3 * R ^ 3 := by
        ring

  have hPrefactorNonneg :
      0
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
      (T - t) ^ 2 := by

    positivity

  have hScaledSix :
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
        (T - t) ^ 2
          *
        h3TopCharacteristicFrequencyAt u t ^ 6
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
        (T - t) ^ 2
          *
        (C ^ 3 * R ^ 3) :=
    mul_le_mul_of_nonneg_left
      hSix
      hPrefactorNonneg

  calc
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
      (T - t) ^ 2
        *
      h3TopCharacteristicFrequencyAt u t ^ 6 :=
      hFrequency

    _ ≤
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
      (T - t) ^ 2
        *
      (C ^ 3 * R ^ 3) :=
      hScaledSix

    _ =
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
      C ^ 3
        *
      (T - t) ^ 2
        *
      R ^ 3 := by
      ring

    _ =
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
        velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t
      ) ^ 3 := by

      rfl

/-! ## Full dissipation normalized by full H³ energy -/

/--
The same inverse-`2/3` cubic rate holds for full H³ dissipation normalized by
full H³ energy.
-/
theorem eventually_normalized_dissipation_cubic_rate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
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
      ) ^ 3 := by

  have hTopRate :=
    eventually_normalized_dissipation3_cubic_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  filter_upwards
    [hTopRate]
    with t hRate

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

  have hE0 :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  have hANonneg :
      0 ≤ A := by

    dsimp only [A]

    positivity

  have hEnergyNonneg :
      0 ≤ velocityH3EnergyAt u t := by

    have hOne :=
      one_le_velocityH3EnergyAt
        u t

    linarith

  have hTop :
      velocityH3Dissipation3At u t
        ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt
      u t

  have hRatio :
      velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t
        ≤
      velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t :=
    div_le_div_of_nonneg_right
      hTop
      hEnergyNonneg

  have hTopRatioNonneg :
      0
        ≤
      velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t :=
    div_nonneg
      (velocityH3Dissipation3At_nonneg
        u t)
      hEnergyNonneg

  have hCube :
      (
        velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t
      ) ^ 3
        ≤
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      ) ^ 3 :=
    pow_le_pow_left₀
      hTopRatioNonneg
      hRatio
      3

  have hScaled :
      A
          *
        (
          velocityH3Dissipation3At u t
            /
          velocityH3EnergyAt u t
        ) ^ 3
        ≤
      A
          *
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        ) ^ 3 :=
    mul_le_mul_of_nonneg_left
      hCube
      hANonneg

  dsimp only [A] at hScaled

  exact
    le_trans
      hRate
      hScaled

/-! ## Sharp normalized balance-gap rate -/

/--
Using the exact identity

    G = 2 D/E,

the normalized balance gap carries the sharp factor-eight cubic rate.
-/
theorem eventually_normalized_balanceGap_cubic_rate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
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
      ) ^ 3 := by

  have hDissRate :=
    eventually_normalized_dissipation_cubic_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  have hClassTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT
      hClass.terminal_start.2

  filter_upwards
    [
      hDissRate,
      hClassTail
    ]
    with t hRate ht

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

  let R : ℝ :=
    velocityH3DissipationAt u t
      /
    velocityH3EnergyAt u t

  let G : ℝ :=
    (
      (
        - velocityH3TransportDerivativeAt u t
      )
        -
      deriv (velocityH3EnergyAt u) t
    )
      /
    velocityH3EnergyAt u t

  have hGap :
      G = 2 * R := by

    dsimp only [G, R]

    exact
      normalized_negativeTransport_sub_deriv_eq_two_mul_dissipation_div_energy
        hH3
        hClass
        ht

  have hRateA :
      1 ≤ A * R ^ 3 := by

    dsimp only [A, R]

    exact
      hRate

  have hEight :
      8 ≤ 8 * (A * R ^ 3) := by
    nlinarith

  have hAlgebra :
      8 * (A * R ^ 3)
        =
      A * G ^ 3 := by

    rw [hGap]

    ring

  rw [hAlgebra] at hEight

  dsimp only [A, G] at hEight ⊢

  exact
    hEight

/-! ## Explicit strict-tail form for full normalized dissipation -/

/--
Strict-tail form of the quantitative normalized full-dissipation rate.
-/
theorem exists_terminalTail_normalized_dissipation_cubic_rate_of_noH3PathExtension
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
        ) ^ 3 := by

  have hEventually :=
    eventually_normalized_dissipation_cubic_rate_of_noH3PathExtension
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

end

end Euclidean
end Bridge
end PrimeTensor
