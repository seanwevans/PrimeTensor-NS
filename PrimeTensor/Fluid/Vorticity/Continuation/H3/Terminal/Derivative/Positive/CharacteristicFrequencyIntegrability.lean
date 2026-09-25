import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicLengthRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Integrability

/-!
# Terminal nonintegrability of the characteristic frequency cube

The quantitative characteristic-frequency theorem gives, on a sufficiently
late terminal tail,

    1
      ≤
    C (T-t)^2 Λ₃(t)^6,

where

    C = 3 K^2 (E₀(b)+1) > 0.

All factors are nonnegative, so taking the nonnegative square root gives

    1
      ≤
    sqrt(C) (T-t) Λ₃(t)^3,

hence

    1 / (T-t)
      ≤
    sqrt(C) Λ₃(t)^3.

The reciprocal terminal-distance profile is already known to be nonintegrable
on every nontrivial interval ending at `T`.  Therefore the cube of the
intrinsic top-order characteristic frequency cannot be integrable on a
terminal H³ energy-class tail of a hypothetical nonextendible path.

This is the intrinsic-frequency analogue of the previously proved
nonintegrability of the top H³ dissipation.  It remains a necessary condition
on the nonextension branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Harmonic lower bound for the frequency cube -/

/--
On a sufficiently late terminal tail,

    1 / (T-t)
      ≤
    sqrt(3 K² (E₀(b)+1)) Λ₃(t)^3.
-/
theorem exists_terminalTail_one_div_terminalDistance_le_sqrtCoefficient_mul_characteristicFrequency_pow_three_of_noH3PathExtension
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
        Real.sqrt
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
          )
          *
        h3TopCharacteristicFrequencyAt u t ^ 3 := by

  obtain
    ⟨c, hc, hRate⟩ :=
    exists_terminalTail_characteristicFrequency_pow_six_rate_of_noH3PathExtension
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

  let C : ℝ :=
    3
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 2
      *
    (
      velocityH3Energy0At u b
        +
      1
    )

  have hE0 :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  have hC :
      0 ≤ C := by

    dsimp only [C]

    positivity

  have hDist :
      0 < T - t := by
    linarith [ht.2]

  have hFrequency :
      0 ≤ h3TopCharacteristicFrequencyAt u t :=
    h3TopCharacteristicFrequencyAt_nonneg
      u t

  have hFrequencyCube :
      0 ≤ h3TopCharacteristicFrequencyAt u t ^ 3 :=
    pow_nonneg
      hFrequency
      3

  have hRateC :
      1
        ≤
      C
        *
      (T - t) ^ 2
        *
      h3TopCharacteristicFrequencyAt u t ^ 6 := by

    dsimp only [C]

    simpa only [mul_assoc] using
      hRate
        t
        ht

  let S : ℝ :=
    Real.sqrt C
      *
    (T - t)
      *
    h3TopCharacteristicFrequencyAt u t ^ 3

  have hSNonneg :
      0 ≤ S := by

    dsimp only [S]

    positivity

  have hSquare :
      S ^ 2
        =
      C
        *
      (T - t) ^ 2
        *
      h3TopCharacteristicFrequencyAt u t ^ 6 := by

    dsimp only [S]

    rw [
      mul_pow,
      mul_pow,
      Real.sq_sqrt hC
    ]

    ring

  have hSquareRate :
      (1 : ℝ) ^ 2
        ≤
      S ^ 2 := by

    rw [one_pow, hSquare]

    exact
      hRateC

  have hLinear :
      1 ≤ S :=
    (sq_le_sq₀
      (by norm_num : (0 : ℝ) ≤ 1)
      hSNonneg).1
      hSquareRate

  apply
    (div_le_iff₀ hDist).2

  dsimp only [S] at hLinear

  calc
    1
        ≤
      Real.sqrt C
        *
      (T - t)
        *
      h3TopCharacteristicFrequencyAt u t ^ 3 :=
      hLinear

    _ =
      (
        Real.sqrt C
          *
        h3TopCharacteristicFrequencyAt u t ^ 3
      )
        *
      (T - t) := by
      ring


/-! ## Nonintegrability of Λ₃³ -/

/--
On every strict subtail of an H³ energy-class tail, hypothetical nonextension
forces the cube of the intrinsic characteristic top-order frequency to be
nonintegrable.
-/
theorem not_integrableOn_characteristicFrequency_pow_three_on_strictSubtail_of_noH3PathExtension
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
        (
          fun t : ℝ =>
            h3TopCharacteristicFrequencyAt u t ^ 3
        )
        (Set.Ioo b T) := by

  obtain
    ⟨c, hc, hHarmonic⟩ :=
    exists_terminalTail_one_div_terminalDistance_le_sqrtCoefficient_mul_characteristicFrequency_pow_three_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  intro hFrequencyIntegrable

  have hFrequencyIntegrableTail :
      MeasureTheory.IntegrableOn
        (
          fun t : ℝ =>
            h3TopCharacteristicFrequencyAt u t ^ 3
        )
        (Set.Ioo c T) := by

    apply
      hFrequencyIntegrable.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hc.1 ht.1,
        ht.2
      ⟩

  let A : ℝ :=
    Real.sqrt
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
      )

  have hANonneg :
      0 ≤ A := by

    dsimp only [A]

    exact
      Real.sqrt_nonneg _

  have hScaled :
      MeasureTheory.IntegrableOn
        (
          fun t : ℝ =>
            A
              *
            h3TopCharacteristicFrequencyAt u t ^ 3
        )
        (Set.Ioo c T) := by

    change
      MeasureTheory.Integrable
        (
          fun t : ℝ =>
            A
              *
            h3TopCharacteristicFrequencyAt u t ^ 3
        )
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo c T))

    exact
      hFrequencyIntegrableTail.const_mul
        A

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

      have hFrequencyNonneg :
          0 ≤ h3TopCharacteristicFrequencyAt u t :=
        h3TopCharacteristicFrequencyAt_nonneg
          u t

      have hFrequencyCubeNonneg :
          0 ≤ h3TopCharacteristicFrequencyAt u t ^ 3 :=
        pow_nonneg
          hFrequencyNonneg
          3

      have hScaledNonneg :
          0
            ≤
          A
            *
          h3TopCharacteristicFrequencyAt u t ^ 3 :=
        mul_nonneg
          hANonneg
          hFrequencyCubeNonneg

      rw [
        Real.norm_eq_abs,
        abs_of_pos
          (one_div_pos.mpr hDist)
      ]

      dsimp only [A]

      exact
        hHarmonic
          t
          ht

  exact
    not_integrableOn_one_div_terminalDistance
      hc.2
      hReciprocal

/--
In particular, the characteristic-frequency cube is nonintegrable on the
original H³ energy-class terminal tail.
-/
theorem not_integrableOn_characteristicFrequency_pow_three_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ MeasureTheory.IntegrableOn
        (
          fun t : ℝ =>
            h3TopCharacteristicFrequencyAt u t ^ 3
        )
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
    not_integrableOn_characteristicFrequency_pow_three_on_strictSubtail_of_noH3PathExtension
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

end

end Euclidean
end Bridge
end PrimeTensor
