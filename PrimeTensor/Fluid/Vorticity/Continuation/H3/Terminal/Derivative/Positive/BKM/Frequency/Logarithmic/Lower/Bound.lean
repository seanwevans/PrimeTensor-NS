import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.BKM.Frequency.Forcing

/-!
# Explicit vorticity lower requirement from the terminal frequency cascade

The previous increment proved that, under hypothetical nonextension, every
sufficiently late positive-growth time satisfies

    2 Λ₃(t)^2
      <
    C_b * 4422 * (B_b + 1)
      * (1 + |g(t)|)
      * (1 + log E(t)),

for every vorticity envelope `g`, where

    C_b = 4 + 3 E₀(b),

and

    B_b =
      h3BKMCanonicalSelectedLogGradientConstant
        (sqrt(E₀(b))).

The positive-growth frequency-amplitude corridor also gives

    E(t)
      ≤
    A_b Λ₃(t)^6,

with

    A_b =
      (4 + 3 E₀(b)) (E₀(b) + 1).

Since `E(t) ≥ 1`, the amplitude upper bound is positive and the logarithm is
monotone:

    1 + log E(t)
      ≤
    1 + log(A_b Λ₃(t)^6).

Substitution yields

    2 Λ₃(t)^2
      <
    K_b (1 + |g(t)|)
      (1 + log(A_b Λ₃(t)^6)),

where

    K_b = C_b * 4422 * (B_b + 1).

All factors in the denominator are strictly positive, so this can be solved
for the vorticity factor:

    2 Λ₃(t)^2
    -------------------------------  <  1 + |g(t)|.
    K_b (1 + log(A_b Λ₃(t)^6))

Thus hypothetical nonextension requires every admissible vorticity envelope to
carry at least a characteristic-frequency-square divided by a logarithmic
frequency factor at every sufficiently late positive-growth time.

This remains a necessary condition, not an assertion that a singular branch
exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Under hypothetical nonextension, every vorticity envelope satisfies an
explicit frequency-square / logarithmic-frequency lower requirement at every
sufficiently late positive-growth time.
-/
theorem exists_terminalTail_positiveGrowth_characteristicFrequency_sq_over_log_le_vorticityEnvelope_of_noH3PathExtension
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
          h3TopCharacteristicFrequencyAt u t ^ 2
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
            1
              +
            Real.log
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
                  *
                h3TopCharacteristicFrequencyAt u t ^ 6
              )
          )
        )
          <
        1 + |g t| := by

  obtain
    ⟨
      cBKM,
      hcBKM,
      hBKM
    ⟩ :=
    exists_terminalTail_positiveGrowth_characteristicFrequency_sq_lt_canonicalBKM_vorticityLogFactor_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb
      hg

  obtain
    ⟨
      cAmp,
      hcAmp,
      hAmp
    ⟩ :=
    exists_terminalTail_positiveGrowth_characteristicFrequencyAmplitudeCorridor_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  let c : ℝ :=
    max cBKM cAmp

  have hcT :
      c < T := by
    dsimp only [c]
    exact
      max_lt
        hcBKM.2
        hcAmp.2

  have hbc :
      b < c := by
    dsimp only [c]
    exact
      lt_of_lt_of_le
        hcBKM.1
        (le_max_left cBKM cAmp)

  refine
    ⟨
      c,
      ⟨hbc, hcT⟩,
      ?_
    ⟩

  intro t ht hDerivative

  have htBKM :
      t ∈ Set.Ioo cBKM T :=
    ⟨
      lt_of_le_of_lt
        (le_max_left cBKM cAmp)
        ht.1,
      ht.2
    ⟩

  have htAmp :
      t ∈ Set.Ioo cAmp T :=
    ⟨
      lt_of_le_of_lt
        (le_max_right cBKM cAmp)
        ht.1,
      ht.2
    ⟩

  have hBKMAt :=
    hBKM
      t
      htBKM
      hDerivative

  have hAmpAt :=
    (hAmp
      t
      htAmp
      hDerivative).2

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

  let Q : ℝ :=
    A
      *
    h3TopCharacteristicFrequencyAt u t ^ 6

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

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt
      u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hAmpQ :
      velocityH3EnergyAt u t
        ≤
      Q := by

    dsimp only [Q, A, C]

    exact
      hAmpAt

  have hQOne :
      1 ≤ Q :=
    hEOne.trans
      hAmpQ

  have hQPos :
      0 < Q := by
    linarith

  have hLogMono :
      Real.log (velocityH3EnergyAt u t)
        ≤
      Real.log Q :=
    Real.strictMonoOn_log.monotoneOn
      hEPos
      hQPos
      hAmpQ

  have hLogFactor :
      1 + Real.log (velocityH3EnergyAt u t)
        ≤
      1 + Real.log Q :=
    add_le_add_right
      hLogMono
      1

  have hBKMK :
      2
          *
        h3TopCharacteristicFrequencyAt u t ^ 2
        <
      K
        *
      (1 + |g t|)
        *
      (1 + Real.log (velocityH3EnergyAt u t)) := by

    dsimp only [K, C, B]

    simpa only [mul_assoc] using
      hBKMAt

  have hPrefactorNonneg :
      0
        ≤
      K * (1 + |g t|) :=
    mul_nonneg
      (le_of_lt hKPos)
      (by positivity)

  have hRhsMono :
      K
          *
        (1 + |g t|)
          *
        (1 + Real.log (velocityH3EnergyAt u t))
        ≤
      K
          *
        (1 + |g t|)
          *
        (1 + Real.log Q) :=
    mul_le_mul_of_nonneg_left
      hLogFactor
      hPrefactorNonneg

  have hSubstituted :
      2
          *
        h3TopCharacteristicFrequencyAt u t ^ 2
        <
      K
        *
      (1 + |g t|)
        *
      (1 + Real.log Q) :=
    lt_of_lt_of_le
      hBKMK
      hRhsMono

  have hLogQNonneg :
      0 ≤ Real.log Q :=
    Real.log_nonneg
      hQOne

  have hLogQFactorPos :
      0 < 1 + Real.log Q := by
    linarith

  have hDenPos :
      0
        <
      K * (1 + Real.log Q) :=
    mul_pos
      hKPos
      hLogQFactorPos

  have hSolved :
      (
        2
          *
        h3TopCharacteristicFrequencyAt u t ^ 2
      )
        /
      (
        K * (1 + Real.log Q)
      )
        <
      1 + |g t| := by

    apply
      (div_lt_iff₀ hDenPos).2

    calc
      2
          *
        h3TopCharacteristicFrequencyAt u t ^ 2
          <
        K
          *
        (1 + |g t|)
          *
        (1 + Real.log Q) :=
        hSubstituted

      _ =
        (1 + |g t|)
          *
        (
          K
            *
          (1 + Real.log Q)
        ) := by
        ring

  dsimp only [K, Q, A, C, B] at hSolved

  exact
    hSolved

end

end Euclidean
end Bridge
end PrimeTensor
