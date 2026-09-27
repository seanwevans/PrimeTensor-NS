import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.DissipationRiccatiCompetition
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicFrequencyRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.FullEnergyNormalizedCascade

/-!
# Positive-growth characteristic-frequency / amplitude corridor

On a hypothetical nonextension branch, the full H³ energy is eventually
comparable from above to the top-order energy block:

    E(t) ≤ C_b E₃(t),

with

    C_b = 4 + 3 E₀(b).

The canonical top characteristic frequency satisfies

    Λ₃(t)^2 = D₃(t) / E₃(t),

and the top dissipation obeys `D₃ ≤ D`.  Therefore, on the same late tail,

    Λ₃(t)^2
      ≤
    C_b D(t) / E(t).

At every positive-growth time the retained-dissipation competition gives

    2 D(t) / E(t)
      <
    K sqrt(E(t)).

Combining the two inequalities yields

    2 Λ₃(t)^2
      <
    C_b K sqrt(E(t)).

The existing Fourier interpolation estimate gives the opposite-direction
amplitude control

    E₃(t)
      ≤
    (E₀(b)+1) Λ₃(t)^6,

and hence, using `E ≤ C_b E₃`,

    E(t)
      ≤
    C_b (E₀(b)+1) Λ₃(t)^6.

Thus every sufficiently late positive-growth time on a hypothetical
nonextendible H³ path lies in the frequency-amplitude corridor

    2 Λ₃² < C_b K sqrt(E)
    E ≤ C_b (E₀(b)+1) Λ₃⁶.

This is a necessary scaling restriction, not an existence statement for a
singular branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Convert top-frequency scale to full normalized dissipation -/

/--
If the full H³ energy is bounded above by `C * E₃`, then the canonical
top-frequency square is bounded by `C * D/E`.
-/
theorem h3TopCharacteristicFrequencyAt_sq_le_coefficient_mul_dissipation_div_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t C : ℝ}
    (_hC :
      0 < C)
    (hEnergyUpper :
      velocityH3EnergyAt u t
        ≤
      C * velocityH3Energy3At u t) :
    h3TopCharacteristicFrequencyAt u t ^ 2
      ≤
    C
      *
    (
      velocityH3DissipationAt u t
        /
      velocityH3EnergyAt u t
    ) := by

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt
      u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hE3Nonneg :
      0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg
      u t

  have hE3Pos :
      0 < velocityH3Energy3At u t := by

    by_contra hNot

    have hE3LeZero :
        velocityH3Energy3At u t ≤ 0 :=
      le_of_not_gt
        hNot

    have hE3Zero :
        velocityH3Energy3At u t = 0 :=
      le_antisymm
        hE3LeZero
        hE3Nonneg

    rw [hE3Zero, mul_zero] at hEnergyUpper

    linarith

  have hDNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg
      u t

  have hRatioNonneg :
      0
        ≤
      velocityH3DissipationAt u t
        /
      velocityH3EnergyAt u t :=
    div_nonneg
      hDNonneg
      (le_of_lt hEPos)

  have hD3Le :
      velocityH3Dissipation3At u t
        ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt
      u t

  have hScaledEnergy :
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      )
        *
      velocityH3EnergyAt u t
        ≤
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      )
        *
      (
        C * velocityH3Energy3At u t
      ) :=
    mul_le_mul_of_nonneg_left
      hEnergyUpper
      hRatioNonneg

  have hDIdentity :
      velocityH3DissipationAt u t
        =
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      )
        *
      velocityH3EnergyAt u t :=
    (
      div_mul_cancel₀
        (velocityH3DissipationAt u t)
        (ne_of_gt hEPos)
    ).symm

  have hD3Scaled :
      velocityH3Dissipation3At u t
        ≤
      (
        C
          *
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        )
      )
        *
      velocityH3Energy3At u t := by

    calc
      velocityH3Dissipation3At u t
          ≤
        velocityH3DissipationAt u t :=
        hD3Le

      _ =
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        )
          *
        velocityH3EnergyAt u t :=
        hDIdentity

      _ ≤
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        )
          *
        (
          C * velocityH3Energy3At u t
        ) :=
        hScaledEnergy

      _ =
        (
          C
            *
          (
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
          )
        )
          *
        velocityH3Energy3At u t := by
        ring

  rw [
    h3TopCharacteristicFrequencyAt_sq
      u t
  ]

  exact
    (div_le_iff₀ hE3Pos).2
      hD3Scaled

/-! ## Late-tail frequency / amplitude corridor -/

/--
Fix a strict terminal anchor `b` and write

    C_b = 4 + 3 E₀(b).

Under hypothetical nonextension there is a later tail such that every
positive-growth time satisfies both

    2 Λ₃² < C_b K sqrt(E)

and

    E ≤ C_b (E₀(b)+1) Λ₃⁶.
-/
theorem exists_terminalTail_positiveGrowth_characteristicFrequencyAmplitudeCorridor_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hb :
      b ∈ Set.Ioo a T) :
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
            <
          (
            4
              +
            3 * velocityH3Energy0At u b
          )
            *
          h3PathSqrtEnergyRiccatiCoefficient
            *
          Real.sqrt
            (velocityH3EnergyAt u t)
        )
          ∧
        (
          velocityH3EnergyAt u t
            ≤
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
            *
          h3TopCharacteristicFrequencyAt u t ^ 6
        ) := by

  let C : ℝ :=
    4
      +
    3 * velocityH3Energy0At u b

  have hE0Nonneg :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  have hCPos :
      0 < C := by
    dsimp only [C]
    linarith

  have hEnergyUpperEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        velocityH3EnergyAt u t
          ≤
        C * velocityH3Energy3At u t := by

    dsimp only [C]

    exact
      eventually_velocityH3EnergyAt_le_anchorCoefficient_mul_energy3_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hb

  obtain
    ⟨
      d,
      hdT,
      hdSubset
    ⟩ :=
    (
      mem_nhdsLT_iff_exists_Ioo_subset
    ).1
      hEnergyUpperEventually

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

  intro t ht hDerivative

  have htD :
      t ∈ Set.Ioo d T :=
    ⟨
      lt_trans
        (
          lt_of_le_of_lt
            (le_max_left d b)
            hMaxC
        )
        ht.1,
      ht.2
    ⟩

  have htB :
      t ∈ Set.Ioo b T :=
    ⟨
      lt_trans hc.1 ht.1,
      ht.2
    ⟩

  have htClass :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hb.1 htB.1,
      htB.2
    ⟩

  have hEnergyUpper :
      velocityH3EnergyAt u t
        ≤
      C * velocityH3Energy3At u t :=
    hdSubset
      htD

  have hFrequencyRatio :
      h3TopCharacteristicFrequencyAt u t ^ 2
        ≤
      C
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      ) :=
    h3TopCharacteristicFrequencyAt_sq_le_coefficient_mul_dissipation_div_energy
      hCPos
      hEnergyUpper

  have hCompetition :
      2
          *
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        )
        <
      h3PathSqrtEnergyRiccatiCoefficient
          *
        Real.sqrt
          (velocityH3EnergyAt u t) :=
    two_mul_dissipation_div_energy_lt_riccati_mul_sqrtEnergy_of_pos_deriv
      hH3
      hClass
      htClass
      hDerivative

  have hFrequencyScaled :
      2
          *
        h3TopCharacteristicFrequencyAt u t ^ 2
        ≤
      2
          *
        (
          C
            *
          (
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
          )
        ) :=
    mul_le_mul_of_nonneg_left
      hFrequencyRatio
      (by norm_num)

  have hCompetitionScaled :
      C
          *
        (
          2
            *
          (
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
          )
        )
        <
      C
          *
        (
          h3PathSqrtEnergyRiccatiCoefficient
            *
          Real.sqrt
            (velocityH3EnergyAt u t)
        ) :=
    mul_lt_mul_of_pos_left
      hCompetition
      hCPos

  have hFrequencyAmplitude :
      2
          *
        h3TopCharacteristicFrequencyAt u t ^ 2
        <
      C
        *
      h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt
        (velocityH3EnergyAt u t) := by

    calc
      2
          *
        h3TopCharacteristicFrequencyAt u t ^ 2
          ≤
        2
          *
        (
          C
            *
          (
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
          )
        ) :=
        hFrequencyScaled

      _ =
        C
          *
        (
          2
            *
          (
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
          )
        ) := by
        ring

      _ <
        C
          *
        (
          h3PathSqrtEnergyRiccatiCoefficient
            *
          Real.sqrt
            (velocityH3EnergyAt u t)
        ) :=
        hCompetitionScaled

      _ =
        C
          *
        h3PathSqrtEnergyRiccatiCoefficient
          *
        Real.sqrt
          (velocityH3EnergyAt u t) := by
        ring

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt
      u t

  have hE3Nonneg :
      0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg
      u t

  have hE3Pos :
      0 < velocityH3Energy3At u t := by

    by_contra hNot

    have hE3LeZero :
        velocityH3Energy3At u t ≤ 0 :=
      le_of_not_gt
        hNot

    have hE3Zero :
        velocityH3Energy3At u t = 0 :=
      le_antisymm
        hE3LeZero
        hE3Nonneg

    rw [hE3Zero, mul_zero] at hEnergyUpper

    linarith

  have hIntrinsic :
      velocityH3Energy3At u t
        ≤
      (
        velocityH3Energy0At u b
          +
        1
      )
        *
      h3TopCharacteristicFrequencyAt u t ^ 6 :=
    velocityH3Energy3At_le_energy0Anchor_add_one_mul_characteristicFrequency_pow_six
      hH3
      hClass
      hb
      htB
      hE3Pos

  have hScaledIntrinsic :
      C * velocityH3Energy3At u t
        ≤
      C
        *
      (
        (
          velocityH3Energy0At u b
            +
          1
        )
          *
        h3TopCharacteristicFrequencyAt u t ^ 6
      ) :=
    mul_le_mul_of_nonneg_left
      hIntrinsic
      (le_of_lt hCPos)

  have hAmplitudeFrequency :
      velocityH3EnergyAt u t
        ≤
      C
        *
      (
        velocityH3Energy0At u b
          +
        1
      )
        *
      h3TopCharacteristicFrequencyAt u t ^ 6 := by

    calc
      velocityH3EnergyAt u t
          ≤
        C * velocityH3Energy3At u t :=
        hEnergyUpper

      _ ≤
        C
          *
        (
          (
            velocityH3Energy0At u b
              +
            1
          )
            *
          h3TopCharacteristicFrequencyAt u t ^ 6
        ) :=
        hScaledIntrinsic

      _ =
        C
          *
        (
          velocityH3Energy0At u b
            +
          1
        )
          *
        h3TopCharacteristicFrequencyAt u t ^ 6 := by
        ring

  dsimp only [C] at hFrequencyAmplitude hAmplitudeFrequency

  exact
    ⟨
      hFrequencyAmplitude,
      hAmplitudeFrequency
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
