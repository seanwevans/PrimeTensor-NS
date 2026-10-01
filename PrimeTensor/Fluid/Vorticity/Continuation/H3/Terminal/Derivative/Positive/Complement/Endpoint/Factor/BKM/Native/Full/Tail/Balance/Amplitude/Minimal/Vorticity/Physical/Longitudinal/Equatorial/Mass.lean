import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Endpoint.Mechanism

/-!
# Quantitative equatorial concentration of a surviving longitudinal H³ defect

The preceding files established two facts.

1. For a fixed coordinate `i`, divergence-free Fourier geometry recovers the
   longitudinal component from the two transverse components on every angular
   good cone

       κ * |ξ| ≤ |ξᵢ|.

2. If physical vorticity component `i` has a pathwise strong H³ endpoint, then
   the longitudinal H³ defect becomes pairwise Cauchy on every fixed good cone.

This file converts those statements into an exact mass decomposition and a
quantitative bad-cone lower bound.

The angular bad cone is exactly the complement of the good cone.  Therefore
the total scaled longitudinal square defect decomposes as

    total = good-cone mass + bad-cone mass.

The total mass is also exactly

    κ² * ‖Gᵢ - Hᵢ‖².

Consequently, if two sufficiently late strict times still have longitudinal
H³ separation at least `ε`, while the physical-vorticity endpoint makes the
good-cone contribution small, a definite amount of mass must remain in the
equatorial bad cone.

This remains a conditional necessary mechanism: it applies when a genuine
longitudinal pairwise non-Cauchy defect is present.  The separate terminal
representation branch from the previous file is not identified with this
mechanism.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The bad cone is the complement of the good cone -/

/--
The strict angular bad cone is exactly the complement of the closed angular
good cone.
-/
theorem h3TerminalLongitudinalAngularBadCone_eq_compl_goodCone
    (i : Fin 3)
    (κ : ℝ) :
    h3TerminalLongitudinalAngularBadCone i κ
      =
    (h3TerminalLongitudinalAngularGoodCone i κ)ᶜ := by

  ext ξ

  simp only [
    h3TerminalLongitudinalAngularBadCone,
    h3TerminalLongitudinalAngularGoodCone,
    Set.mem_setOf_eq,
    Set.mem_compl_iff
  ]

  exact
    (not_le).symm

/--
The angular bad cone is measurable.
-/
theorem measurableSet_h3TerminalLongitudinalAngularBadCone
    (i : Fin 3)
    (κ : ℝ) :
    MeasurableSet
      (h3TerminalLongitudinalAngularBadCone i κ) := by

  rw [
    h3TerminalLongitudinalAngularBadCone_eq_compl_goodCone
  ]

  exact
    (
      measurableSet_h3TerminalLongitudinalAngularGoodCone
        i κ
    ).compl

/--
The good and bad cones are disjoint.
-/
theorem disjoint_h3TerminalLongitudinalAngularGoodCone_badCone
    (i : Fin 3)
    (κ : ℝ) :
    Disjoint
      (h3TerminalLongitudinalAngularGoodCone i κ)
      (h3TerminalLongitudinalAngularBadCone i κ) := by

  rw [
    h3TerminalLongitudinalAngularBadCone_eq_compl_goodCone
  ]

  exact
    disjoint_compl_right

/--
The good and bad cones cover all Fourier frequencies.
-/
theorem union_h3TerminalLongitudinalAngularGoodCone_badCone
    (i : Fin 3)
    (κ : ℝ) :
    h3TerminalLongitudinalAngularGoodCone i κ
        ∪
      h3TerminalLongitudinalAngularBadCone i κ
      =
    Set.univ := by

  rw [
    h3TerminalLongitudinalAngularBadCone_eq_compl_goodCone
  ]

  exact
    union_compl_self
      (h3TerminalLongitudinalAngularGoodCone i κ)

/-! ## Total and bad-cone square defects -/

/--
Total scaled longitudinal square defect of two weighted H³ spectral vector
states.
-/
noncomputable def h3TerminalLongitudinalTotalScaledSquareDefect
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    (
      κ *
        ‖h3TerminalSpectralDifferenceAt G H i ξ‖
    ) ^ 2

/--
Scaled longitudinal square defect restricted to the angular bad cone.
-/
noncomputable def h3TerminalLongitudinalBadConeScaledSquareDefect
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
    (
      κ *
        ‖h3TerminalSpectralDifferenceAt G H i ξ‖
    ) ^ 2

/-! ## Integrability of the scaled defect density -/

/--
The raw pointwise square difference of one spectral component is integrable.
-/
private theorem h3TerminalSpectralDifferenceAt_sq_integrable_equatorialMass
    (G H : H3SpectralFinVectorState)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖h3TerminalSpectralDifferenceAt G H i ξ‖ ^ 2)
      volume := by

  simpa [
    h3TerminalSpectralDifferenceAt
  ] using
    h3FourierComplexL2_pointwise_sub_norm_sq_integrable
      (G i)
      (H i)

/--
The scaled longitudinal square-defect density is integrable on all Fourier
space.
-/
private theorem h3TerminalLongitudinalScaledSquareDensity_integrable
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        (
          κ *
            ‖h3TerminalSpectralDifferenceAt G H i ξ‖
        ) ^ 2)
      volume := by

  have hBase :=
    h3TerminalSpectralDifferenceAt_sq_integrable_equatorialMass
      G H i

  have hScaled :=
    hBase.const_mul
      (κ ^ 2)

  refine
    hScaled.congr
      ?_

  filter_upwards with ξ

  ring

/-! ## Exact total-mass identities -/

/--
The total scaled defect is exactly `κ²` times the bundled H³ norm-square
difference of the selected component.
-/
theorem h3TerminalLongitudinalTotalScaledSquareDefect_eq
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalLongitudinalTotalScaledSquareDefect
        i κ G H
      =
    κ ^ 2 * ‖G i - H i‖ ^ 2 := by

  unfold
    h3TerminalLongitudinalTotalScaledSquareDefect

  calc
    (∫ ξ : H3FourierPoint3,
        (
          κ *
            ‖h3TerminalSpectralDifferenceAt G H i ξ‖
        ) ^ 2)
        =
      ∫ ξ : H3FourierPoint3,
        κ ^ 2 *
          ‖h3TerminalSpectralDifferenceAt G H i ξ‖ ^ 2 := by

          apply integral_congr_ae

          filter_upwards with ξ

          ring

    _ =
      κ ^ 2 *
        ∫ ξ : H3FourierPoint3,
          ‖h3TerminalSpectralDifferenceAt G H i ξ‖ ^ 2 := by

          rw [integral_const_mul]

    _ =
      κ ^ 2 * ‖G i - H i‖ ^ 2 := by

          congr 1

          simpa [
            h3TerminalSpectralDifferenceAt
          ] using
            (
              h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                (G i)
                (H i)
            ).symm

/--
The total scaled defect splits exactly into good-cone and bad-cone masses.
-/
theorem h3TerminalLongitudinalTotalScaledSquareDefect_eq_good_add_bad
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalLongitudinalTotalScaledSquareDefect
        i κ G H
      =
    h3TerminalLongitudinalGoodConeScaledSquareDefect
        i κ G H
      +
    h3TerminalLongitudinalBadConeScaledSquareDefect
        i κ G H := by

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      (
        κ *
          ‖h3TerminalSpectralDifferenceAt G H i ξ‖
      ) ^ 2

  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularGoodCone i κ

  let B : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularBadCone i κ

  have hInt :
      Integrable f volume := by

    dsimp only [f]

    exact
      h3TerminalLongitudinalScaledSquareDensity_integrable
        i κ G H

  have hS :
      MeasurableSet S := by

    dsimp only [S]

    exact
      measurableSet_h3TerminalLongitudinalAngularGoodCone
        i κ

  have hB :
      MeasurableSet B := by

    dsimp only [B]

    exact
      measurableSet_h3TerminalLongitudinalAngularBadCone
        i κ

  have hDisjoint :
      Disjoint S B := by

    dsimp only [S, B]

    exact
      disjoint_h3TerminalLongitudinalAngularGoodCone_badCone
        i κ

  have hUnion :
      S ∪ B = Set.univ := by

    dsimp only [S, B]

    exact
      union_h3TerminalLongitudinalAngularGoodCone_badCone
        i κ

  unfold
    h3TerminalLongitudinalTotalScaledSquareDefect
    h3TerminalLongitudinalGoodConeScaledSquareDefect
    h3TerminalLongitudinalBadConeScaledSquareDefect

  change
    (∫ ξ : H3FourierPoint3, f ξ)
      =
    (∫ ξ in S, f ξ)
      +
    (∫ ξ in B, f ξ)

  calc
    (∫ ξ : H3FourierPoint3, f ξ)
        =
      ∫ ξ in Set.univ, f ξ := by
        simp

    _ =
      ∫ ξ in S ∪ B, f ξ := by
        rw [hUnion]

    _ =
      (∫ ξ in S, f ξ)
        +
      (∫ ξ in B, f ξ) := by

        exact
          setIntegral_union
            hDisjoint
            hB
            hInt.integrableOn
            hInt.integrableOn

/-! ## Quantitative bad-cone lower bound -/

/--
If the selected component has bundled H³ separation at least `ε`, then a small
good-cone contribution forces a positive bad-cone contribution.

The lower bound is deliberately stated with a factor `1/2`, leaving slack for
the pathwise specialization.
-/
theorem h3TerminalLongitudinalBadConeScaledSquareDefect_gt_half
    {i : Fin 3}
    {κ ε : ℝ}
    (hκ : 0 ≤ κ)
    (hε : 0 ≤ ε)
    {G H : H3SpectralFinVectorState}
    (hLarge :
      ε ≤ ‖G i - H i‖)
    (hGood :
      h3TerminalLongitudinalGoodConeScaledSquareDefect
          i κ G H
        <
      (κ ^ 2 * ε ^ 2) / 2) :
    (κ ^ 2 * ε ^ 2) / 2
      <
    h3TerminalLongitudinalBadConeScaledSquareDefect
      i κ G H := by

  have hSq :
      ε ^ 2
        ≤
      ‖G i - H i‖ ^ 2 :=
    (
      sq_le_sq₀
        hε
        (norm_nonneg _)
    ).2
      hLarge

  have hκsq :
      0 ≤ κ ^ 2 :=
    sq_nonneg κ

  have hTotalLower :
      κ ^ 2 * ε ^ 2
        ≤
      h3TerminalLongitudinalTotalScaledSquareDefect
        i κ G H := by

    rw [
      h3TerminalLongitudinalTotalScaledSquareDefect_eq
    ]

    exact
      mul_le_mul_of_nonneg_left
        hSq
        hκsq

  have hSplit :=
    h3TerminalLongitudinalTotalScaledSquareDefect_eq_good_add_bad
      i κ G H

  linarith

/-! ## Pathwise equatorial concentration -/

/--
Suppose physical vorticity component `i` has a pathwise strong H³ endpoint.

For any fixed aperture `κ > 0` and separation scale `ε > 0`, sufficiently late
strict times have the following property:

if the longitudinal H³ component states are still separated by at least `ε`,
then the angular bad cone carries more than half of the scaled defect mass
`κ² ε²`.

Thus any genuine late longitudinal pairwise non-Cauchy separation is forced
into the equatorial angular region.
-/
theorem longitudinalBadConeScaledSquareDefect_gt_half_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    {κ ε : ℝ}
    (hκ : 0 < κ)
    (hε : 0 < ε) :
    ∃ η : ℝ,
      0 < η
        ∧
      ∀
        (s : ℝ)
        (hs : s ∈ Set.Ioo (0 : ℝ) T)
        (t : ℝ)
        (ht : t ∈ Set.Ioo (0 : ℝ) T),
        dist s T < η →
        dist t T < η →
        ε
          ≤
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
                hH3 i s hs
              -
            h3TerminalVelocityComponentSpectralStateAt
                hH3 i t ht
          ) →
        (κ ^ 2 * ε ^ 2) / 2
          <
        h3TerminalLongitudinalBadConeScaledSquareDefect
          i κ
          (h3TerminalVelocitySpectralStateAt hH3 s hs)
          (h3TerminalVelocitySpectralStateAt hH3 t ht) := by

  let r : ℝ :=
    κ * ε / 4

  have hr :
      0 < r := by

    dsimp only [r]

    positivity

  obtain
    ⟨
      η,
      hη,
      hGoodNear
    ⟩ :=
    longitudinalGoodConeScaledSquareDefect_lt_four_mul_sq_of_actualVorticityStrongH3EndpointPath
      hH3
      hPhysical
      hκ
      hr

  refine
    ⟨
      η,
      hη,
      ?_
    ⟩

  intro s hs t ht hsT htT hLarge

  let Gs : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 s hs

  let Gt : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t ht

  have hGoodRaw :
      h3TerminalLongitudinalGoodConeScaledSquareDefect
          i κ Gs Gt
        <
      4 * r ^ 2 := by

    dsimp only [Gs, Gt]

    exact
      hGoodNear
        s hs t ht
        hsT htT

  have hGood :
      h3TerminalLongitudinalGoodConeScaledSquareDefect
          i κ Gs Gt
        <
      (κ ^ 2 * ε ^ 2) / 2 := by

    have hQuarter :
        4 * r ^ 2
          <
        (κ ^ 2 * ε ^ 2) / 2 := by

      dsimp only [r]

      nlinarith [
        mul_pos hκ hε
      ]

    exact
      hGoodRaw.trans
        hQuarter

  have hLarge' :
      ε
        ≤
      ‖Gs i - Gt i‖ := by

    dsimp only [Gs, Gt]

    simpa only [
      h3TerminalVelocitySpectralStateAt_apply
    ] using
      hLarge

  exact
    h3TerminalLongitudinalBadConeScaledSquareDefect_gt_half
      hκ.le
      hε.le
      hLarge'
      hGood

end

end Euclidean
end Bridge
end PrimeTensor
