import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.NormalizedDissipationThresholdContinuation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Integrability

/-!
# Critical normalized H³ dissipation integrability frontier

The quantitative normalized full-dissipation rate under hypothetical
nonextension is

    1
      ≤
    A_b (T-t)^2 (D(t)/E(t))^3,

where

    A_b =
      3 K^2 (E₀(b)+1) (4+3E₀(b))^3.

Write

    R(t) = D(t)/E(t)

and

    Q(t) = R(t) * sqrt(R(t)).

Since `R(t) ≥ 0`,

    Q(t)^2 = R(t)^3.

Thus the cubic rate is exactly a squared rate for `Q`.  With the harmless fixed
coefficient

    B_b = A_b + 1,

one obtains on a sufficiently late tail

    1 / (T-t) ≤ B_b Q(t).

The reciprocal terminal-distance profile is nonintegrable.  Therefore
hypothetical nonextension forces

    Q ∉ L^1((b,T))

on every strict terminal subtail.  In standard notation this is the critical
normalized-dissipation condition

    (D/E)^(3/2) ∉ L^1.

The file also records the positive continuation contrapositives: integrability
of this critical quantity on one strict terminal subtail is sufficient for
smooth continuation across `T`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Critical normalized dissipation density -/

/--
The real-valued critical `3/2` normalized dissipation density

    (D/E) * sqrt(D/E).

Using this explicit real form avoids introducing `Real.rpow`.
-/
noncomputable def h3NormalizedDissipationThreeHalvesAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    (
      velocityH3DissipationAt u t
        /
      velocityH3EnergyAt u t
    )
      *
    Real.sqrt
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      )

/--
The normalized full dissipation ratio is nonnegative.
-/
theorem velocityH3DissipationAt_div_energyAt_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0
      ≤
    velocityH3DissipationAt u t
      /
    velocityH3EnergyAt u t := by

  have hEnergyNonneg :
      0 ≤ velocityH3EnergyAt u t := by

    have hOne :=
      one_le_velocityH3EnergyAt
        u t

    linarith

  exact
    div_nonneg
      (velocityH3DissipationAt_nonneg
        u t)
      hEnergyNonneg

/--
The square of the critical `3/2` density is exactly the cube of the normalized
dissipation ratio.
-/
theorem h3NormalizedDissipationThreeHalvesAt_sq
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    h3NormalizedDissipationThreeHalvesAt u t ^ 2
      =
    (
      velocityH3DissipationAt u t
        /
      velocityH3EnergyAt u t
    ) ^ 3 := by

  have hRatioNonneg :=
    velocityH3DissipationAt_div_energyAt_nonneg
      u t

  unfold h3NormalizedDissipationThreeHalvesAt

  rw [
    mul_pow,
    Real.sq_sqrt hRatioNonneg
  ]

  ring

/--
The critical `3/2` density is nonnegative.
-/
theorem h3NormalizedDissipationThreeHalvesAt_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3NormalizedDissipationThreeHalvesAt u t := by

  unfold h3NormalizedDissipationThreeHalvesAt

  exact
    mul_nonneg
      (
        velocityH3DissipationAt_div_energyAt_nonneg
          u t
      )
      (Real.sqrt_nonneg _)

/-! ## Harmonic lower bound -/

/--
On a sufficiently late terminal tail, hypothetical nonextension forces the
harmonic lower bound

    1/(T-t)
      ≤
    (A_b + 1) * (D/E) * sqrt(D/E),

where

    A_b = 3 K² (E₀(b)+1) (4+3E₀(b))³.
-/
theorem exists_terminalTail_one_div_terminalDistance_le_normalizedDissipationThreeHalves_of_noH3PathExtension
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
        1 / (T - t)
          ≤
        (
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
            +
          1
        )
          *
        h3NormalizedDissipationThreeHalvesAt u t := by

  obtain
    ⟨c, hc, hRate⟩ :=
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

  intro t ht

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

  let B : ℝ :=
    A + 1

  let Q : ℝ :=
    h3NormalizedDissipationThreeHalvesAt u t

  have hE0 :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  have hA :
      0 ≤ A := by

    dsimp only [A]

    positivity

  have hBPos :
      0 < B := by

    dsimp only [B]

    linarith

  have hBNonneg :
      0 ≤ B :=
    le_of_lt hBPos

  have hDist :
      0 < T - t := by
    linarith [ht.2]

  have hQNonneg :
      0 ≤ Q := by

    dsimp only [Q]

    exact
      h3NormalizedDissipationThreeHalvesAt_nonneg
        u t

  have hRateA :
      1
        ≤
      A
        *
      (T - t) ^ 2
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      ) ^ 3 := by

    dsimp only [A]

    simpa only [mul_assoc] using
      hRate
        t
        ht

  have hQSquare :
      Q ^ 2
        =
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      ) ^ 3 := by

    dsimp only [Q]

    exact
      h3NormalizedDissipationThreeHalvesAt_sq
        u t

  have hRateQ :
      1
        ≤
      A
        *
      (T - t) ^ 2
        *
      Q ^ 2 := by

    rw [hQSquare]

    exact
      hRateA

  have hAB :
      A ≤ B ^ 2 := by

    dsimp only [B]

    nlinarith

  have hFactorNonneg :
      0
        ≤
      (T - t) ^ 2
        *
      Q ^ 2 :=
    mul_nonneg
      (sq_nonneg _)
      (sq_nonneg _)

  have hScaled :
      A
          *
        (T - t) ^ 2
          *
        Q ^ 2
        ≤
      B ^ 2
          *
        (T - t) ^ 2
          *
        Q ^ 2 := by

    calc
      A
          *
        (T - t) ^ 2
          *
        Q ^ 2
          =
        A
          *
        (
          (T - t) ^ 2
            *
          Q ^ 2
        ) := by
          ring

      _ ≤
        B ^ 2
          *
        (
          (T - t) ^ 2
            *
          Q ^ 2
        ) :=
        mul_le_mul_of_nonneg_right
          hAB
          hFactorNonneg

      _ =
        B ^ 2
          *
        (T - t) ^ 2
          *
        Q ^ 2 := by
          ring

  let S : ℝ :=
    B * (T - t) * Q

  have hSNonneg :
      0 ≤ S := by

    dsimp only [S]

    exact
      mul_nonneg
        (
          mul_nonneg
            hBNonneg
            (le_of_lt hDist)
        )
        hQNonneg

  have hSquare :
      S ^ 2
        =
      B ^ 2
        *
      (T - t) ^ 2
        *
      Q ^ 2 := by

    dsimp only [S]

    ring

  have hSquareRate :
      (1 : ℝ) ^ 2
        ≤
      S ^ 2 := by

    rw [
      one_pow,
      hSquare
    ]

    exact
      le_trans
        hRateQ
        hScaled

  have hLinear :
      1 ≤ S :=
    (sq_le_sq₀
      (by norm_num : (0 : ℝ) ≤ 1)
      hSNonneg).1
      hSquareRate

  apply
    (div_le_iff₀ hDist).2

  dsimp only [S, Q, B, A] at hLinear ⊢

  calc
    1
        ≤
      (
        (
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
            +
          1
        )
          *
        (T - t)
      )
        *
      h3NormalizedDissipationThreeHalvesAt u t :=
      hLinear

    _ =
      (
        (
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
            +
          1
        )
          *
        h3NormalizedDissipationThreeHalvesAt u t
      )
        *
      (T - t) := by
      ring

/-! ## Critical nonintegrability -/

/--
On every strict terminal subtail, hypothetical nonextension forces the critical
normalized dissipation `3/2` density to be nonintegrable.
-/
theorem not_integrableOn_normalizedDissipationThreeHalves_on_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ¬ MeasureTheory.IntegrableOn
        (h3NormalizedDissipationThreeHalvesAt u)
        (Set.Ioo b T) := by

  obtain
    ⟨c, hc, hHarmonic⟩ :=
    exists_terminalTail_one_div_terminalDistance_le_normalizedDissipationThreeHalves_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  intro hCriticalIntegrable

  have hCriticalIntegrableTail :
      MeasureTheory.IntegrableOn
        (h3NormalizedDissipationThreeHalvesAt u)
        (Set.Ioo c T) := by

    apply
      hCriticalIntegrable.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hc.1 ht.1,
        ht.2
      ⟩

  let B : ℝ :=
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
      +
    1

  have hE0 :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  have hBNonneg :
      0 ≤ B := by

    dsimp only [B]

    positivity

  have hScaled :
      MeasureTheory.IntegrableOn
        (
          fun t : ℝ =>
            B
              *
            h3NormalizedDissipationThreeHalvesAt u t
        )
        (Set.Ioo c T) := by

    change
      MeasureTheory.Integrable
        (
          fun t : ℝ =>
            B
              *
            h3NormalizedDissipationThreeHalvesAt u t
        )
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo c T))

    exact
      hCriticalIntegrableTail.const_mul
        B

  have hReciprocal :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => 1 / (T - t))
        (Set.Ioo c T) := by

    apply
      Integrable.mono'
        hScaled

    · exact
        (
          show
            Measurable
              (fun t : ℝ => 1 / (T - t))
          by
            fun_prop
        ).aestronglyMeasurable

    · filter_upwards
        [
          ae_restrict_mem
            measurableSet_Ioo
        ]
        with t ht

      have hDist :
          0 < T - t := by
        linarith [ht.2]

      have hCriticalNonneg :
          0 ≤ h3NormalizedDissipationThreeHalvesAt u t :=
        h3NormalizedDissipationThreeHalvesAt_nonneg
          u t

      have hScaledNonneg :
          0
            ≤
          B
            *
          h3NormalizedDissipationThreeHalvesAt u t :=
        mul_nonneg
          hBNonneg
          hCriticalNonneg

      rw [
        Real.norm_eq_abs,
        abs_of_pos
          (one_div_pos.mpr hDist)
      ]

      dsimp only [B]

      exact
        hHarmonic
          t
          ht

  exact
    not_integrableOn_one_div_terminalDistance
      hc.2
      hReciprocal

/--
In particular, the critical normalized dissipation `3/2` density is
nonintegrable on the original H³ energy-class tail.
-/
theorem not_integrableOn_normalizedDissipationThreeHalves_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ MeasureTheory.IntegrableOn
        (h3NormalizedDissipationThreeHalvesAt u)
        (Set.Ioo a T) := by

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  have hNotTail :=
    not_integrableOn_normalizedDissipationThreeHalves_on_strictSubtail_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  intro hIntegrable

  apply hNotTail

  apply
    hIntegrable.mono_set

  intro t ht

  exact
    ⟨
      lt_trans hb.1 ht.1,
      ht.2
    ⟩

/-! ## Continuation criteria -/

/--
Integrability of the critical normalized dissipation `3/2` density on one
strict terminal subtail forces smooth continuation across `T`.
-/
theorem exists_smoothContinuationExtension_of_integrableOn_normalizedDissipationThreeHalves_on_strictSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hIntegrable :
      MeasureTheory.IntegrableOn
        (h3NormalizedDissipationThreeHalvesAt u)
        (Set.Ioo b T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  exact
    (
      not_integrableOn_normalizedDissipationThreeHalves_on_strictSubtail_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hb
    )
      hIntegrable

/--
Integrability of the critical normalized dissipation `3/2` density on the
whole energy-class tail also forces smooth continuation.
-/
theorem exists_smoothContinuationExtension_of_integrableOn_normalizedDissipationThreeHalves_on_energyClassTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hIntegrable :
      MeasureTheory.IntegrableOn
        (h3NormalizedDissipationThreeHalvesAt u)
        (Set.Ioo a T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  exact
    (
      not_integrableOn_normalizedDissipationThreeHalves_on_energyClassTail_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    )
      hIntegrable

/--
Neutral critical-integrability dichotomy.

Either smooth continuation exists, or the normalized dissipation `3/2`
density is nonintegrable on every strict terminal subtail.
-/
theorem smoothContinuationExtension_or_normalizedDissipationThreeHalves_nonintegrable_on_every_strictSubtail
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
      ∀ b : ℝ,
        b ∈ Set.Ioo a T →
        ¬ MeasureTheory.IntegrableOn
            (h3NormalizedDissipationThreeHalvesAt u)
            (Set.Ioo b T)
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

    intro b hb

    exact
      not_integrableOn_normalizedDissipationThreeHalves_on_strictSubtail_of_noH3PathExtension
        hH3
        hExtension
        hClass
        hb

end

end Euclidean
end Bridge
end PrimeTensor
