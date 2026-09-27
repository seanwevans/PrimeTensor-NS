import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.BKMFrequencyLinearLowerBound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.FullEnergyTransportSequence

/-!
# Vorticity-envelope divergence on the canonical positive-growth sequence

The linear BKM frequency lower bound proved that, under hypothetical
nonextension, every sufficiently late positive-growth time satisfies

    2 Λ₃(t)
    ---------  <  1 + |g(t)|,
       D_b

for every scalar vorticity envelope `g`, where `D_b > 0` is one fixed
anchor-dependent constant.

The canonical positive-growth terminal sequence `σ_n` already satisfies

    σ_n -> T,
    n < E'(σ_n),

and carries

    E(σ_n) -> +∞,
    D(σ_n) / E(σ_n) -> +∞,
    (-T_H3(σ_n)) / E(σ_n) -> +∞.

The full terminal characteristic-frequency limit also gives

    Λ₃(σ_n) -> +∞.

Since `σ_n` eventually enters the tail on which the linear BKM estimate holds,
the fixed positive denominator `D_b` can be absorbed into an arbitrary target
threshold `M`.  Therefore

    |g(σ_n)| -> +∞.

Thus every admissible scalar vorticity envelope diverges in magnitude on the
same canonical positive-energy-growth sequence that carries the full H³
energy/dissipation/transport cascade.

This is stronger than existence of one actual vorticity blowup sequence:
the conclusion applies to every function satisfying the vorticity-envelope
interface on the chosen terminal tail.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Under hypothetical nonextension, every scalar vorticity envelope on a strict
terminal tail diverges in magnitude along one canonical positive-growth
sequence.  The same sequence simultaneously carries full H³ energy,
normalized dissipation, normalized adverse transport, and characteristic
frequency divergence.
-/
theorem exists_terminal_positiveGrowth_fullCascade_vorticityEnvelope_tendsto_atTop_of_noH3PathExtension
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
    ∃ σ : ℕ → ℝ,
      (
        ∀ n : ℕ,
          σ n ∈ Set.Ioo a T
            ∧
          σ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          (n : ℝ)
            <
          deriv (velocityH3EnergyAt u) (σ n)
      )
        ∧
      Tendsto σ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3EnergyAt u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            velocityH3DissipationAt u (σ n)
              /
            velocityH3EnergyAt u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            (
              - velocityH3TransportDerivativeAt u (σ n)
            )
              /
            velocityH3EnergyAt u (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicFrequencyAt
              u
              (σ n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            |g (σ n)|
        )
        atTop
        atTop := by

  obtain
    ⟨
      c,
      hc,
      hLinear
    ⟩ :=
    exists_terminalTail_positiveGrowth_characteristicFrequency_linear_lt_vorticityEnvelope_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb
      hg

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      hTransportRatioTendsto
    ⟩ :=
    exists_terminal_fullEnergyTransportCascade_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hSigmaLT :
      Tendsto
        σ
        atTop
        (𝓝[<] T) := by

    refine
      tendsto_nhdsWithin_iff.mpr
        ?_

    exact
      ⟨
        hSigmaTendsto,
        Eventually.of_forall
          (
            fun n =>
              (hσ n).1.2
          )
      ⟩

  have hFrequencyTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicFrequencyAt
              u
              (σ n)
        )
        atTop
        atTop :=
    (
      h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    ).comp
      hSigmaLT

  have hEventuallyInLinearTail :
      ∀ᶠ n : ℕ in atTop,
        c < σ n :=
    (tendsto_order.1 hSigmaTendsto).1
      c
      hc.2

  let C : ℝ :=
    4
      +
    3 * velocityH3Energy0At u b

  let B : ℝ :=
    h3BKMCanonicalSelectedLogGradientConstant
      (Real.sqrt
        (velocityH3Energy0At u b))

  let A : ℝ :=
    C
      *
    (
      velocityH3Energy0At u b
        +
      1
    )

  let D : ℝ :=
    (
      C
        *
      4422
        *
      (B + 1)
    )
      *
    (A + 7)

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

  have hAPos :
      0 < A := by

    dsimp only [A]

    exact
      mul_pos
        hCPos
        (by linarith)

  have hDPos :
      0 < D := by

    dsimp only [D]

    exact
      mul_pos
        (
          mul_pos
            (
              mul_pos
                hCPos
                (by norm_num)
            )
            (by linarith)
        )
        (by linarith)

  have hEnvelopeTendsto :
      Tendsto
        (
          fun n : ℕ =>
            |g (σ n)|
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    by_cases hM :
        M ≤ 0

    · exact
        Eventually.of_forall
          (
            fun n =>
              le_trans
                hM
                (abs_nonneg
                  (g (σ n)))
          )

    · have hMPos :
          0 < M :=
        lt_of_not_ge
          hM

      let R : ℝ :=
        D * (M + 2)

      have hFrequencyEventually :
          ∀ᶠ n : ℕ in atTop,
            R
              ≤
            h3TopCharacteristicFrequencyAt
              u
              (σ n) :=
        hFrequencyTendsto.eventually
          (eventually_ge_atTop R)

      filter_upwards
        [
          hEventuallyInLinearTail,
          hFrequencyEventually
        ]
        with n hcn hFrequencyN

      have hTailN :
          σ n ∈ Set.Ioo c T :=
        ⟨
          hcn,
          (hσ n).1.2
        ⟩

      have hDerivativeN :
          0
            <
          deriv (velocityH3EnergyAt u) (σ n) := by

        have hnNonneg :
            0 ≤ (n : ℝ) :=
          Nat.cast_nonneg n

        exact
          lt_of_le_of_lt
            hnNonneg
            (hσ n).2.2

      have hLinearN :
          (
            2
              *
            h3TopCharacteristicFrequencyAt
              u
              (σ n)
          )
            /
          D
            <
          1 + |g (σ n)| := by

        dsimp only [D, A, C, B]

        exact
          hLinear
            (σ n)
            hTailN
            hDerivativeN

      have hFrequencyLower :
          D * (M + 2)
            ≤
          h3TopCharacteristicFrequencyAt
            u
            (σ n) := by

        simpa only [R] using
          hFrequencyN

      have hThreshold :
          M + 1
            <
          (
            2
              *
            h3TopCharacteristicFrequencyAt
              u
              (σ n)
          )
            /
          D := by

        apply
          (lt_div_iff₀ hDPos).2

        have hPositiveMargin :
            0 < D * (M + 3) :=
          mul_pos
            hDPos
            (by linarith)

        nlinarith

      have hMAbs :
          M < |g (σ n)| := by
        linarith

      exact
        le_of_lt
          hMAbs

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      hTransportRatioTendsto,
      hFrequencyTendsto,
      hEnvelopeTendsto
    ⟩

/--
Neutral formulation: either smooth continuation exists, or every specified
vorticity envelope on the chosen strict tail admits the synchronized
positive-growth divergence package above.
-/
theorem smoothContinuationExtension_or_terminal_positiveGrowth_fullCascade_vorticityEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {g : ℝ → ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
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
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T
    )
      ∨
    (
      ∃ σ : ℕ → ℝ,
        (
          ∀ n : ℕ,
            σ n ∈ Set.Ioo a T
              ∧
            σ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
              ∧
            (n : ℝ)
              <
            deriv (velocityH3EnergyAt u) (σ n)
        )
          ∧
        Tendsto σ atTop (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              velocityH3EnergyAt u (σ n)
          )
          atTop
          atTop
          ∧
        Tendsto
          (
            fun n : ℕ =>
              velocityH3DissipationAt u (σ n)
                /
              velocityH3EnergyAt u (σ n)
          )
          atTop
          atTop
          ∧
        Tendsto
          (
            fun n : ℕ =>
              (
                - velocityH3TransportDerivativeAt u (σ n)
              )
                /
              velocityH3EnergyAt u (σ n)
          )
          atTop
          atTop
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TopCharacteristicFrequencyAt
                u
                (σ n)
          )
          atTop
          atTop
          ∧
        Tendsto
          (
            fun n : ℕ =>
              |g (σ n)|
          )
          atTop
          atTop
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          exists_terminal_positiveGrowth_fullCascade_vorticityEnvelope_tendsto_atTop_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
            hg
        )

end

end Euclidean
end Bridge
end PrimeTensor
