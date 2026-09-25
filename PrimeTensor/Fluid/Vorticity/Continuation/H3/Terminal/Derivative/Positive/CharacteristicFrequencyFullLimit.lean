import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicFrequencyThresholdContinuation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.Integrability

/-!
# Full one-sided terminal characteristic-frequency limit

The preceding characteristic-frequency cascade was first packaged along a
selected sequence.  The quantitative terminal rate is stronger: hypothetical
nonextension forces

    1 ≤ C (T-t)^2 Λ₃(t)^6

at every sufficiently late strict time, with one fixed positive coefficient

    C = 3 K^2 (E₀(b)+1).

This implies a full one-sided terminal limit, not merely a subsequential one.

Fix `M > 0`.  Shrink the terminal interval once more until

    2 C M^6 (T-t)^2 ≤ 1.

If `Λ₃(t) < M` at any time in that smaller tail, then

    1
      ≤ C (T-t)^2 Λ₃(t)^6
      < C (T-t)^2 M^6
      ≤ 1/2,

a contradiction.  Therefore

    Λ₃(t) -> +∞  as t ↑ T.

Since

    ℓ₃(t) = Λ₃(t)⁻¹,

the reciprocal characteristic length satisfies the full one-sided limit

    ℓ₃(t) -> 0  as t ↑ T.

This is stronger than the previously selected terminal sequence.  It remains
a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Full left-terminal frequency divergence -/

/--
Hypothetical nonextension forces the intrinsic top-order characteristic
frequency to tend to `+∞` along the full left neighborhood of `T`.
-/
theorem h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (h3TopCharacteristicFrequencyAt u)
      (𝓝[<] T)
      atTop := by

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  obtain
    ⟨cRate, hcRate, hRate⟩ :=
    exists_terminalTail_characteristicFrequency_pow_six_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

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

  have hCPos :
      0 < C := by

    dsimp only [C]

    exact
      mul_pos
        (
          mul_pos
            (by norm_num : (0 : ℝ) < 3)
            (
              pow_pos
                h3PathSqrtEnergyRiccatiCoefficient_pos
                2
            )
        )
        (by linarith)

  refine
    tendsto_atTop.2
      ?_

  intro M

  by_cases hM :
      M ≤ 0

  · exact
      Eventually.of_forall
        (
          fun t =>
            le_trans
              hM
              (h3TopCharacteristicFrequencyAt_nonneg
                u t)
        )

  · have hMPos :
        0 < M :=
      lt_of_not_ge
        hM

    let B : ℝ :=
      2 * C * M ^ 6

    obtain
      ⟨cSmall, hcSmall, hSmall⟩ :=
      exists_terminalTail_const_mul_terminalDistance_sq_le_one
        B
        T
        cRate
        hcRate.2

    show
      {t : ℝ |
        M ≤ h3TopCharacteristicFrequencyAt u t}
        ∈
      𝓝[<] T

    rw [
      mem_nhdsLT_iff_exists_Ioo_subset
    ]

    refine
      ⟨
        cSmall,
        hcSmall.2,
        ?_
      ⟩

    intro t ht

    have htRate :
        t ∈ Set.Ioo cRate T :=
      ⟨
        lt_trans hcSmall.1 ht.1,
        ht.2
      ⟩

    have hRateT :
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
          htRate

    have hSmallT :
        B * (T - t) ^ 2
          ≤
        1 :=
      hSmall
        t
        ht

    have hDistPos :
        0 < T - t := by
      linarith [ht.2]

    have hFrequencyNonneg :
        0 ≤ h3TopCharacteristicFrequencyAt u t :=
      h3TopCharacteristicFrequencyAt_nonneg
        u t

    by_contra hNot

    have hFrequencyLt :
        h3TopCharacteristicFrequencyAt u t
          <
        M :=
      lt_of_not_ge
        hNot

    have hPowLt :
        h3TopCharacteristicFrequencyAt u t ^ 6
          <
        M ^ 6 :=
      pow_lt_pow_left₀
        hFrequencyLt
        hFrequencyNonneg
        (by norm_num)

    have hPrefactorPos :
        0
          <
        C * (T - t) ^ 2 := by
      positivity

    have hScaledLt :
        C
            *
          (T - t) ^ 2
            *
          h3TopCharacteristicFrequencyAt u t ^ 6
          <
        C
            *
          (T - t) ^ 2
            *
          M ^ 6 :=
      mul_lt_mul_of_pos_left
        hPowLt
        hPrefactorPos

    have hOneLt :
        1
          <
        C
            *
          (T - t) ^ 2
            *
          M ^ 6 :=
      lt_of_le_of_lt
        hRateT
        hScaledLt

    have hDouble :
        2
            *
          (
            C
              *
            (T - t) ^ 2
              *
            M ^ 6
          )
          ≤
        1 := by

      calc
        2
            *
          (
            C
              *
            (T - t) ^ 2
              *
            M ^ 6
          )
            =
          B * (T - t) ^ 2 := by

            dsimp only [B]

            ring

        _ ≤
          1 :=
          hSmallT

    linarith

/-! ## Full left-terminal length collapse -/

/--
Under hypothetical nonextension the reciprocal characteristic top-order length
tends to zero along the full left neighborhood of `T`.
-/
theorem h3TopCharacteristicLengthAt_tendsto_zero_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (h3TopCharacteristicLengthAt u)
      (𝓝[<] T)
      (𝓝 0) := by

  have hFrequency :=
    h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hInverse :
      Tendsto
        (
          fun t : ℝ =>
            (h3TopCharacteristicFrequencyAt u t)⁻¹
        )
        (𝓝[<] T)
        (𝓝 0) :=
    hFrequency.inv_tendsto_atTop

  change
    Tendsto
      (
        fun t : ℝ =>
          (h3TopCharacteristicFrequencyAt u t)⁻¹
      )
      (𝓝[<] T)
      (𝓝 0)

  exact
    hInverse

/-! ## Neutral full-terminal dichotomy -/

/--
Neutral full-terminal formulation:

* either the H³ path extends smoothly across `T`;
* or the characteristic frequency tends to `+∞` and its reciprocal length
  tends to zero along the entire left terminal neighborhood.

The theorem does not select a branch.
-/
theorem smoothContinuationExtension_or_full_characteristicFrequencyCascade
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
      Tendsto
        (h3TopCharacteristicFrequencyAt u)
        (𝓝[<] T)
        atTop
        ∧
      Tendsto
        (h3TopCharacteristicLengthAt u)
        (𝓝[<] T)
        (𝓝 0)
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
        ⟨
          h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          h3TopCharacteristicLengthAt_tendsto_zero_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass
        ⟩

/-! ## Positive continuation contrapositives -/

/--
Failure of full left-terminal characteristic-frequency divergence forces smooth
continuation.
-/
theorem exists_smoothContinuationExtension_of_not_characteristicFrequency_tendsto_atTop_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNotFrequency :
      ¬ Tendsto
          (h3TopCharacteristicFrequencyAt u)
          (𝓝[<] T)
          atTop) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  exact
    hNotFrequency
      (
        h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
          hH3
          hNoExtension
          hClass
      )

/--
Failure of full left-terminal characteristic-length collapse forces smooth
continuation.
-/
theorem exists_smoothContinuationExtension_of_not_characteristicLength_tendsto_zero_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNotLength :
      ¬ Tendsto
          (h3TopCharacteristicLengthAt u)
          (𝓝[<] T)
          (𝓝 0)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  exact
    hNotLength
      (
        h3TopCharacteristicLengthAt_tendsto_zero_nhdsLT_of_noH3PathExtension
          hH3
          hNoExtension
          hClass
      )

end

end Euclidean
end Bridge
end PrimeTensor
