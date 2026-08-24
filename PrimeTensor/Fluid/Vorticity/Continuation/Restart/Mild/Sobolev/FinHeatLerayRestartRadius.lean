import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralRealizabilityBridge

/-!
# Explicit positive restart radius for the finite H³ heat--Leray problem

The concrete Picard construction requires

    8 * C(ν) * A * sqrt τ ≤ 1.

This file removes that hypothesis from future restart statements by choosing a
canonical positive lifespan depending only on `ν` and the positive H³ bound
`A`.

We use

    r(ν,A) = 8 * C(ν) * A,
    δ(ν,A) = (1 / (r(ν,A) + 1))^2.

Since `r ≥ 0`, the denominator is strictly positive, `δ > 0`, and

    r * sqrt δ = r / (r + 1) ≤ 1.

The final section packages the Banach-selected mild path at this canonical
radius, so downstream continuation theorems no longer need to carry a separate
small-time hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Canonical radius -/

/-- Dimensionless size entering the concrete Picard smallness condition. -/
def h3FinHeatLerayRestartScale
    (ν A : ℝ) : ℝ :=
  8 * h3HeatLerayDuhamelPathCoefficient ν * A

/-- The restart scale is nonnegative whenever the H³ bound is nonnegative. -/
theorem h3FinHeatLerayRestartScale_nonneg
    (ν : ℝ)
    {A : ℝ}
    (hA : 0 ≤ A) :
    0 ≤ h3FinHeatLerayRestartScale ν A := by
  unfold h3FinHeatLerayRestartScale
  exact
    mul_nonneg
      (mul_nonneg (by norm_num) (h3HeatLerayDuhamelPathCoefficient_nonneg ν))
      hA

/--
Canonical physical restart lifespan.

The added `+ 1` avoids any division-by-zero split, including the degenerate
case where the Duhamel coefficient vanishes.
-/
def h3FinHeatLerayRestartRadius
    (ν A : ℝ) : ℝ :=
  (1 / (h3FinHeatLerayRestartScale ν A + 1)) ^ 2

/-- The canonical restart lifespan is strictly positive for every positive H³ bound. -/
theorem h3FinHeatLerayRestartRadius_pos
    (ν : ℝ)
    {A : ℝ}
    (hA : 0 < A) :
    0 < h3FinHeatLerayRestartRadius ν A := by
  have hscale : 0 ≤ h3FinHeatLerayRestartScale ν A :=
    h3FinHeatLerayRestartScale_nonneg ν hA.le
  have hden : 0 < h3FinHeatLerayRestartScale ν A + 1 := by
    linarith
  unfold h3FinHeatLerayRestartRadius
  exact pow_pos (one_div_pos.mpr hden) 2

/-- The canonical radius automatically satisfies the concrete Picard smallness bound. -/
theorem h3FinHeatLerayRestartRadius_smallness
    (ν : ℝ)
    {A : ℝ}
    (hA : 0 ≤ A) :
    8 * h3HeatLerayDuhamelPathCoefficient ν * A *
        Real.sqrt (h3FinHeatLerayRestartRadius ν A)
      ≤ 1 := by
  have hscale : 0 ≤ h3FinHeatLerayRestartScale ν A :=
    h3FinHeatLerayRestartScale_nonneg ν hA
  have hden : 0 < h3FinHeatLerayRestartScale ν A + 1 := by
    linarith
  have hinv :
      0 ≤ 1 / (h3FinHeatLerayRestartScale ν A + 1) :=
    (one_div_pos.mpr hden).le
  change
    h3FinHeatLerayRestartScale ν A *
        Real.sqrt (h3FinHeatLerayRestartRadius ν A)
      ≤ 1
  unfold h3FinHeatLerayRestartRadius
  rw [Real.sqrt_sq hinv]
  calc
    h3FinHeatLerayRestartScale ν A *
          (1 / (h3FinHeatLerayRestartScale ν A + 1))
        =
      h3FinHeatLerayRestartScale ν A /
          (h3FinHeatLerayRestartScale ν A + 1) := by
        simp only [div_eq_mul_inv, one_mul]
    _ ≤ 1 := by
      apply (div_le_iff₀ hden).2
      linarith

/-- Every positive H³ bound therefore supplies a strictly positive admissible restart time. -/
theorem exists_h3FinHeatLerayRestartRadius
    (ν : ℝ)
    {A : ℝ}
    (hA : 0 < A) :
    ∃ τ : ℝ,
      0 < τ ∧
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1 := by
  refine ⟨h3FinHeatLerayRestartRadius ν A, ?_, ?_⟩
  · exact h3FinHeatLerayRestartRadius_pos ν hA
  · exact h3FinHeatLerayRestartRadius_smallness ν hA.le

/-! ## Canonical Banach-selected path at the restart radius -/

/--
The concrete spectral mild path on the canonical restart interval.  Unlike
`h3SpectralFinHeatLerayMildSolution`, this definition carries no explicit
small-time proof argument.
-/
noncomputable def h3SpectralFinHeatLerayMildSolutionAtRestartRadius
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    H3SpectralVelocityPath :=
  h3SpectralFinHeatLerayMildSolution
    hν
    (h3FinHeatLerayRestartRadius_pos ν hA).le
    U₀ hA hU₀
    (h3FinHeatLerayRestartRadius_smallness ν hA.le)

/-- The canonical-radius path satisfies the concrete heat--Leray mild equation. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_satisfies_mild
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    h3SpectralVelocityHeatFreePath
          ν
          (h3FinHeatLerayRestartRadius ν A)
          hν.le
          (h3FinHeatLerayRestartRadius_pos ν hA).le
          U₀
        +
      h3SpectralFinHeatLerayDuhamelPathOperator
        hν
        (h3FinHeatLerayRestartRadius_pos ν hA).le
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadius
          hν U₀ hA hU₀)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadius
          hν U₀ hA hU₀)
      =
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius
      hν U₀ hA hU₀ := by
  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadius
  exact
    h3SpectralFinHeatLerayMildSolution_satisfies_mild
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)

/-- Every normalized slice of the canonical-radius path remains in the `2A` ball. -/
theorem norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_apply_le_twoA
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (s : H3UnitTime) :
    ‖h3SpectralFinHeatLerayMildSolutionAtRestartRadius
        hν U₀ hA hU₀ s‖
      ≤ 2 * A := by
  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadius
  exact
    norm_h3SpectralFinHeatLerayMildSolution_apply_le_twoA
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      s

end

end Euclidean
end Bridge
end PrimeTensor
