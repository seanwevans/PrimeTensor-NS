import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.BKM.Frequency.Logarithmic.Lower.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Characteristic.Frequency.Full.Limit

/-!
# Linear vorticity requirement from the BKM frequency logarithm

The previous result gives, at every sufficiently late positive-growth time,

    2 Λ₃²
    -------------------------------  <  1 + |g|.
    K_b (1 + log(A_b Λ₃^6))

Because hypothetical nonextension forces the full left-terminal limit

    Λ₃(t) -> +∞,

we may move farther into the terminal tail and assume `1 ≤ Λ₃(t)`.

For

    A_b =
      (4 + 3 E₀(b)) (E₀(b)+1),

we have `A_b > 0`, and therefore

    log(A_b Λ₃^6)
      =
    log A_b + 6 log Λ₃
      ≤
    A_b + 6 Λ₃.

Since `1 ≤ Λ₃`,

    1 + log(A_b Λ₃^6)
      ≤
    (A_b + 7) Λ₃.

Substituting this larger denominator into the previous lower requirement and
cancelling one positive factor of `Λ₃` yields the clean linear condition

    2 Λ₃
    ------------------  <  1 + |g|.
    K_b (A_b + 7)

Thus every vorticity envelope on a hypothetical nonextension branch must grow
at least linearly in the characteristic frequency along sufficiently late
positive-growth times, up to one fixed anchor-dependent constant.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Under hypothetical nonextension, every admissible vorticity envelope satisfies
a fixed positive multiple of the top characteristic frequency below
`1 + |g(t)|` at every sufficiently late positive-growth time.
-/
theorem exists_terminalTail_positiveGrowth_characteristicFrequency_linear_lt_vorticityEnvelope_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {g : ℝ → ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hb :
      b ∈ Set.Ioo a T)
    (hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VorticityEnvelope
            u g s) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        0 < deriv (velocityH3EnergyAt u) t →
        (
          2
            *
          h3TopCharacteristicFrequencyAt u t
        )
          /
        (
          (
            (
              4
                +
              3 * velocityH3Energy0At u b
            )
              *
            4422
              *
            (
              h3BKMCanonicalSelectedLogGradientConstant
                  (Real.sqrt
                    (velocityH3Energy0At u b))
                +
              1
            )
          )
            *
          (
            (
              (
                4
                  +
                3 * velocityH3Energy0At u b
              )
                *
              (
                velocityH3Energy0At u b
                  +
                1
              )
            )
              +
            7
          )
        )
          <
        1 + |g t| := by

  obtain
    ⟨
      cLog,
      hcLog,
      hLogLower
    ⟩ :=
    exists_terminalTail_positiveGrowth_characteristicFrequency_sq_over_log_le_vorticityEnvelope_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb
      hg

  have hFrequencyLimit :=
    h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hFrequencyOneEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        1 ≤ h3TopCharacteristicFrequencyAt u t :=
    hFrequencyLimit.eventually
      (eventually_ge_atTop 1)

  obtain
    ⟨
      cFreq,
      hcFreqT,
      hFreqSubset
    ⟩ :=
    (
      mem_nhdsLT_iff_exists_Ioo_subset
    ).1
      hFrequencyOneEventually

  let c : ℝ :=
    max cLog cFreq

  have hcT :
      c < T := by
    dsimp only [c]
    exact
      max_lt
        hcLog.2
        hcFreqT

  have hbc :
      b < c := by
    dsimp only [c]
    exact
      lt_of_lt_of_le
        hcLog.1
        (le_max_left cLog cFreq)

  refine
    ⟨
      c,
      ⟨hbc, hcT⟩,
      ?_
    ⟩

  intro t ht hDerivative

  have htLog :
      t ∈ Set.Ioo cLog T :=
    ⟨
      lt_of_le_of_lt
        (le_max_left cLog cFreq)
        ht.1,
      ht.2
    ⟩

  have htFreq :
      t ∈ Set.Ioo cFreq T :=
    ⟨
      lt_of_le_of_lt
        (le_max_right cLog cFreq)
        ht.1,
      ht.2
    ⟩

  have hOld :=
    hLogLower
      t
      htLog
      hDerivative

  have hLambdaOne :
      1 ≤ h3TopCharacteristicFrequencyAt u t :=
    hFreqSubset
      htFreq

  let Λ : ℝ :=
    h3TopCharacteristicFrequencyAt u t

  let C : ℝ :=
    4
      +
    3 * velocityH3Energy0At u b

  let B : ℝ :=
    h3BKMCanonicalSelectedLogGradientConstant
      (Real.sqrt
        (velocityH3Energy0At u b))

  let K : ℝ :=
    C * 4422 * (B + 1)

  let A : ℝ :=
    C
      *
    (
      velocityH3Energy0At u b
        +
      1
    )

  have hE0Nonneg :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  have hCPos :
      0 < C := by
    dsimp only [C]
    linarith

  have hBNonneg :
      0 ≤ B := by
    dsimp only [B]
    exact
      h3BKMCanonicalSelectedLogGradientConstant_nonneg
        (Real.sqrt_nonneg _)

  have hKPos :
      0 < K := by
    dsimp only [K]
    exact
      mul_pos
        (
          mul_pos
            hCPos
            (by norm_num)
        )
        (by linarith)

  have hAOne :
      1 ≤ A := by

    have hCOne :
        1 ≤ C := by
      dsimp only [C]
      linarith

    have hE0One :
        1
          ≤
        velocityH3Energy0At u b + 1 := by
      linarith

    dsimp only [A]

    have hProduct :
        1 ≤ C * (velocityH3Energy0At u b + 1) := by

      have hNonneg :
          0
            ≤
          (C - 1)
            *
          ((velocityH3Energy0At u b + 1) - 1) :=
        mul_nonneg
          (sub_nonneg.mpr hCOne)
          (sub_nonneg.mpr hE0One)

      nlinarith

    exact
      hProduct

  have hAPos :
      0 < A := by
    linarith

  have hLambdaOne' :
      1 ≤ Λ := by
    simpa only [Λ] using
      hLambdaOne

  have hLambdaPos :
      0 < Λ := by
    linarith

  have hLambdaNonneg :
      0 ≤ Λ :=
    le_of_lt
      hLambdaPos

  have hLambdaPowPos :
      0 < Λ ^ 6 :=
    pow_pos
      hLambdaPos
      6

  have hQPos :
      0 < A * Λ ^ 6 :=
    mul_pos
      hAPos
      hLambdaPowPos

  have hLogExpand :
      Real.log (A * Λ ^ 6)
        =
      Real.log A
        +
      6 * Real.log Λ := by

    rw [
      Real.log_mul
        (ne_of_gt hAPos)
        (ne_of_gt hLambdaPowPos),
      Real.log_pow
    ]

    norm_num

  have hLogA :
      Real.log A ≤ A :=
    Real.log_le_self
      (le_of_lt hAPos)

  have hLogLambda :
      Real.log Λ ≤ Λ :=
    Real.log_le_self
      hLambdaNonneg

  have hLogQLinear :
      1 + Real.log (A * Λ ^ 6)
        ≤
      (A + 7) * Λ := by

    rw [hLogExpand]

    have hSix :
        6 * Real.log Λ
          ≤
        6 * Λ :=
      mul_le_mul_of_nonneg_left
        hLogLambda
        (by norm_num)

    have hBase :
        1 + Real.log A + 6 * Real.log Λ
          ≤
        1 + A + 6 * Λ := by
      linarith

    have hScale :
        1 + A + 6 * Λ
          ≤
        (A + 7) * Λ := by

      have hAOneScaled :
          A + 1
            ≤
          (A + 1) * Λ :=
        le_mul_of_one_le_right
          (by linarith)
          hLambdaOne'

      nlinarith

    linarith

  have hLambdaPowOne :
      1 ≤ Λ ^ 6 :=
    one_le_pow₀
      hLambdaOne'

  have hQOne :
      1 ≤ A * Λ ^ 6 := by

    have hNonneg :
        0
          ≤
        (A - 1)
          *
        (Λ ^ 6 - 1) :=
      mul_nonneg
        (sub_nonneg.mpr hAOne)
        (sub_nonneg.mpr hLambdaPowOne)

    nlinarith

  have hLogQNonneg :
      0 ≤ Real.log (A * Λ ^ 6) :=
    Real.log_nonneg
      hQOne

  have hLogFactorPos :
      0 < 1 + Real.log (A * Λ ^ 6) := by
    linarith

  have hASevenPos :
      0 < A + 7 := by
    linarith

  have hLargeDenPos :
      0 < K * ((A + 7) * Λ) :=
    mul_pos
      hKPos
      (
        mul_pos
          hASevenPos
          hLambdaPos
      )

  have hSmallDenPos :
      0 < K * (1 + Real.log (A * Λ ^ 6)) :=
    mul_pos
      hKPos
      hLogFactorPos

  have hDenOrder :
      K * (1 + Real.log (A * Λ ^ 6))
        ≤
      K * ((A + 7) * Λ) :=
    mul_le_mul_of_nonneg_left
      hLogQLinear
      (le_of_lt hKPos)

  have hOldLocal :
      (
        2 * Λ ^ 2
      )
        /
      (
        K
          *
        (1 + Real.log (A * Λ ^ 6))
      )
        <
      1 + |g t| := by

    dsimp only [Λ, K, A, C, B]

    exact
      hOld

  have hQuotientOrder :
      (
        2 * Λ ^ 2
      )
        /
      (
        K * ((A + 7) * Λ)
      )
        ≤
      (
        2 * Λ ^ 2
      )
        /
      (
        K * (1 + Real.log (A * Λ ^ 6))
      ) := by

    have hNumeratorNonneg :
        0 ≤ 2 * Λ ^ 2 := by
      positivity

    exact
      div_le_div_of_nonneg_left
        hNumeratorNonneg
        hSmallDenPos
        hDenOrder

  have hLinearRaw :
      (
        2 * Λ ^ 2
      )
        /
      (
        K * ((A + 7) * Λ)
      )
        <
      1 + |g t| :=
    lt_of_le_of_lt
      hQuotientOrder
      hOldLocal

  have hLinear :
      (
        2 * Λ
      )
        /
      (
        K * (A + 7)
      )
        <
      1 + |g t| := by

    have hDenBaseNe :
        K * (A + 7) ≠ 0 :=
      ne_of_gt
        (
          mul_pos
            hKPos
            hASevenPos
        )

    have hLambdaNe :
        Λ ≠ 0 :=
      ne_of_gt
        hLambdaPos

    have hIdentity :
        (
          2 * Λ ^ 2
        )
          /
        (
          K * ((A + 7) * Λ)
        )
          =
        (
          2 * Λ
        )
          /
        (
          K * (A + 7)
        ) := by

      field_simp [
        hDenBaseNe,
        hLambdaNe
      ]

    rw [hIdentity] at hLinearRaw

    exact
      hLinearRaw

  dsimp only [Λ, K, A, C, B] at hLinear

  exact
    hLinear

end

end Euclidean
end Bridge
end PrimeTensor
