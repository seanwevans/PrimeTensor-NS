import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.Expansion
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# L⁴ control of the cutoff boundary derivative

The boundary error in the quartic Landau identity contains the coordinate
directional derivative

    Dχ_R(x) eₐ.

The previously proved operator-norm estimate gives

    ‖Dχ_R(x)‖ ≤ C / R.

This file turns that pointwise estimate into the quantitative `L⁴` estimate
needed by Hölder.  The key additional fact is support:

    supp (Dχ_R · eₐ) ⊆ closedBall 0 (2R).

Thus

    ‖Dχ_R · eₐ‖₄
      ≤ (C / R) · volume(closedBall 0 (2R))^(1/4).

On `Point3`, Haar scaling gives

    volume(closedBall 0 (2R))
      = ofReal ((2R)^3) · volume(closedBall 0 1),

so the right side has the expected `R^(-1/4)` scaling.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticBoundaryNorm
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical coordinate direction has unit norm in the project's
finite-product norm. -/
theorem norm_axisDirection_eq_one_landau
    (a : Axis Depth.three) :
    ‖axisDirection a‖ = 1 := by
  apply le_antisymm

  · rw [pi_norm_le_iff_of_nonneg zero_le_one]

    intro i

    by_cases hia : i = a

    · subst i
      simp [axisDirection]

    · have hOther :
          axisDirection a i = 0 :=
        axisDirection_other
          (i := a)
          (j := i)
          hia

      rw [hOther]
      simp

  · have hCoord :
        ‖axisDirection a a‖
          ≤
        ‖axisDirection a‖ := by
      exact
        (
          pi_norm_le_iff_of_nonneg
            (x := axisDirection a)
            (norm_nonneg (axisDirection a))
        ).1
          le_rfl
          a

    simpa [axisDirection_same] using
      hCoord

/-- The directional derivative of the cutoff is supported inside its outer
radius. -/
theorem support_fderiv_h3LandauCutoffBump_axisDirection_subset_closedBall
    {R : ℝ}
    (hR : 0 < R)
    (a : Axis Depth.three) :
    Function.support
        (fun x : Point3 =>
          fderiv ℝ
              (fun y : Point3 =>
                h3LandauCutoffBump R hR y)
              x
              (axisDirection a))
      ⊆
    Metric.closedBall
      (0 : Point3)
      (2 * R) := by
  intro x hx

  have hxTSupport :
      x ∈
        tsupport
          (fun x : Point3 =>
            fderiv ℝ
                (fun y : Point3 =>
                  h3LandauCutoffBump R hR y)
                x
                (axisDirection a)) :=
    subset_tsupport _ hx

  have hxCutoffTSupport :
      x ∈
        tsupport
          (fun y : Point3 =>
            h3LandauCutoffBump R hR y) :=
    (
      tsupport_fderiv_apply_subset
        (𝕜 := ℝ)
        (f :=
          fun y : Point3 =>
            h3LandauCutoffBump R hR y)
        (axisDirection a)
    )
      hxTSupport

  rw [
    (h3LandauCutoffBump R hR).tsupport_eq
  ] at hxCutoffTSupport

  simpa using
    hxCutoffTSupport

/-- The global operator-norm cutoff estimate also controls every coordinate
directional derivative with the same constant. -/
theorem exists_uniform_norm_fderiv_h3LandauCutoffBump_axisDirection_le_div :
    ∃ C : ℝ≥0,
      ∀ {R : ℝ}
        (hR : 0 < R)
        (a : Axis Depth.three)
        (x : Point3),
          ‖fderiv ℝ
              (fun y : Point3 =>
                h3LandauCutoffBump R hR y)
              x
              (axisDirection a)‖
            ≤
          (C : ℝ) / R := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_norm_fderiv_h3LandauCutoffBump_le_div

  refine ⟨C, ?_⟩

  intro R hR a x

  calc
    ‖fderiv ℝ
        (fun y : Point3 =>
          h3LandauCutoffBump R hR y)
        x
        (axisDirection a)‖
        ≤
      ‖fderiv ℝ
          (fun y : Point3 =>
            h3LandauCutoffBump R hR y)
          x‖
        *
      ‖axisDirection a‖ := by
        exact
          ContinuousLinearMap.le_opNorm
            _
            _

    _ =
      ‖fderiv ℝ
          (fun y : Point3 =>
            h3LandauCutoffBump R hR y)
          x‖ := by
        rw [
          norm_axisDirection_eq_one_landau,
          mul_one
        ]

    _ ≤
      (C : ℝ) / R :=
        hC hR x

/-- Quantitative `L⁴` estimate for a coordinate directional derivative of the
cutoff. -/
theorem exists_uniform_eLpNorm_four_fderiv_h3LandauCutoffBump_axisDirection_le :
    ∃ C : ℝ≥0,
      ∀ {R : ℝ}
        (hR : 0 < R)
        (a : Axis Depth.three),
        eLpNorm
            (fun x : Point3 =>
              fderiv ℝ
                  (fun y : Point3 =>
                    h3LandauCutoffBump R hR y)
                  x
                  (axisDirection a))
            (ENNReal.ofReal 4)
            volume
          ≤
        ENNReal.ofReal ((C : ℝ) / R)
          *
        (
          volume
            (
              Metric.closedBall
                (0 : Point3)
                (2 * R)
            )
        ) ^ (1 / (4 : ℝ)) := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_norm_fderiv_h3LandauCutoffBump_axisDirection_le_div

  refine ⟨C, ?_⟩

  intro R hR a

  let φ : Point3 → ℝ :=
    fun x : Point3 =>
      fderiv ℝ
          (fun y : Point3 =>
            h3LandauCutoffBump R hR y)
          x
          (axisDirection a)

  let s : Set Point3 :=
    Metric.closedBall
      (0 : Point3)
      (2 * R)

  have hφContinuous :
      Continuous φ := by
    dsimp [φ]

    exact
      (
        (h3LandauCutoffBump_spatialC1 hR).continuous_fderiv
          (by norm_num)
      ).clm_apply
        continuous_const

  have hφMeas :
      AEStronglyMeasurable
        φ
        volume :=
    hφContinuous.aestronglyMeasurable

  have hφMeasRestrict :
      AEStronglyMeasurable
        φ
        (volume.restrict s) :=
    hφMeas.restrict

  have hSupport :
      Function.support φ ⊆ s := by
    dsimp [φ, s]

    exact
      support_fderiv_h3LandauCutoffBump_axisDirection_subset_closedBall
        hR a

  have hEq :
      eLpNorm
          φ
          (ENNReal.ofReal 4)
          (volume.restrict s)
        =
      eLpNorm
          φ
          (ENNReal.ofReal 4)
          volume :=
    eLpNorm_restrict_eq_of_support_subset
      hSupport

  have hTop :
      eLpNorm
          φ
          (⊤ : ℝ≥0∞)
          (volume.restrict s)
        ≤
      ENNReal.ofReal ((C : ℝ) / R) := by
    rw [
      eLpNorm_exponent_top
    ]

    apply
      eLpNormEssSup_le_of_ae_bound

    filter_upwards with x

    dsimp [φ]

    exact
      hC hR a x

  have hCompare :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := φ)
      (μ := volume.restrict s)
      (p := ENNReal.ofReal 4)
      (q := (⊤ : ℝ≥0∞))
      (by simp)
      hφMeasRestrict

  rw [← hEq]

  calc
    eLpNorm
        φ
        (ENNReal.ofReal 4)
        (volume.restrict s)
        ≤
      eLpNorm
          φ
          (⊤ : ℝ≥0∞)
          (volume.restrict s)
        *
      (
        (volume.restrict s) Set.univ
      ) ^ (1 / (4 : ℝ)) := by
        simpa using
          hCompare

    _ ≤
      ENNReal.ofReal ((C : ℝ) / R)
        *
      (
        (volume.restrict s) Set.univ
      ) ^ (1 / (4 : ℝ)) := by
        gcongr

    _ =
      ENNReal.ofReal ((C : ℝ) / R)
        *
      (
        volume s
      ) ^ (1 / (4 : ℝ)) := by
        simp [s]

/-- Haar scaling of the radius-`2R` ball in `Point3`. -/
theorem volume_closedBall_point3_two_mul
    {R : ℝ}
    (hR : 0 < R) :
    volume
        (
          Metric.closedBall
            (0 : Point3)
            (2 * R)
        )
      =
    ENNReal.ofReal ((2 * R) ^ 3)
      *
    volume
      (
        Metric.closedBall
          (0 : Point3)
          1
      ) := by
  rw [
    (volume : Measure Point3).addHaar_closedBall'
      (0 : Point3)
      (by positivity)
  ]

  rw [
    point3_finrank_eq_three_landau
  ]

end

end Euclidean
end Bridge
end PrimeTensor
