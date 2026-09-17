import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.BoundaryHolder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Real L⁴ form of the quartic cutoff boundary estimate

`BoundaryNorm` gives the cutoff directional derivative estimate in `eLpNorm`.
For the Bochner Hölder inequality used in the boundary integral, it is useful
to expose the corresponding real-valued `lpNorm` estimate.

The only nontrivial bookkeeping here is finite-valuedness of the closed-ball
measure and the orientation of `ENNReal.toReal_rpow`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticBoundaryReal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real-valued `L⁴` form of the quantitative cutoff derivative bound. -/
theorem exists_uniform_lpNorm_four_fderiv_h3LandauCutoffBump_axisDirection_le :
    ∃ C : ℝ≥0,
      ∀ {R : ℝ}
        (hR : 0 < R)
        (a : Axis Depth.three),
        lpNorm
            (fun x : Point3 =>
              fderiv ℝ
                  (fun y : Point3 =>
                    h3LandauCutoffBump R hR y)
                  x
                  (axisDirection a))
            4
            volume
          ≤
        ((C : ℝ) / R)
          *
        (
          volume
            (
              Metric.closedBall
                (0 : Point3)
                (2 * R)
            )
        ).toReal ^ (1 / (4 : ℝ)) := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_eLpNorm_four_fderiv_h3LandauCutoffBump_axisDirection_le

  refine ⟨C, ?_⟩

  intro R hR a

  let φ : Point3 → ℝ :=
    fun x : Point3 =>
      fderiv ℝ
          (fun y : Point3 =>
            h3LandauCutoffBump R hR y)
          x
          (axisDirection a)

  have hφMeas :
      AEStronglyMeasurable
        φ
        volume := by
    dsimp [φ]

    exact
      (
        (h3LandauCutoffBump_spatialC1 hR).continuous_fderiv
          (by norm_num)
      ).clm_apply
        continuous_const
      |>.aestronglyMeasurable

  have hENN :
      eLpNorm
          φ
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
    simpa [φ] using
      hC hR a

  have hBallNeTop :
      volume
          (
            Metric.closedBall
              (0 : Point3)
              (2 * R)
          )
        ≠
      (⊤ : ℝ≥0∞) :=
    measure_closedBall_lt_top.ne

  have hBallPowNeTop :
      (
        volume
          (
            Metric.closedBall
              (0 : Point3)
              (2 * R)
          )
      ) ^ (1 / (4 : ℝ))
        ≠
      (⊤ : ℝ≥0∞) := by
    exact
      ENNReal.rpow_ne_top_of_nonneg
        (by norm_num)
        hBallNeTop

  have hRightNeTop :
      ENNReal.ofReal ((C : ℝ) / R)
          *
        (
          volume
            (
              Metric.closedBall
                (0 : Point3)
                (2 * R)
            )
        ) ^ (1 / (4 : ℝ))
        ≠
      (⊤ : ℝ≥0∞) := by
    exact
      ENNReal.mul_ne_top
        (by simp)
        hBallPowNeTop

  have hLeftNeTop :
      eLpNorm
          φ
          (ENNReal.ofReal 4)
          volume
        ≠
      (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top
      hRightNeTop
      hENN

  have hReal :=
    (
      ENNReal.toReal_le_toReal
        hLeftNeTop
        hRightNeTop
    ).2
      hENN

  rw [
    MeasureTheory.toReal_eLpNorm hφMeas,
    ENNReal.toReal_mul
  ] at hReal

  rw [
    ENNReal.toReal_ofReal
      (div_nonneg C.coe_nonneg hR.le)
  ] at hReal

  rw [
    ← ENNReal.toReal_rpow
  ] at hReal

  simpa [φ] using
    hReal

end

end Euclidean
end Bridge
end PrimeTensor
