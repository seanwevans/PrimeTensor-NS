import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.DuhamelLocality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Overlap.Path

/-!
# Classicalization: selected restart subinterval consistency

The canonical radius solution is selected by Banach's fixed-point theorem on
the full interval `[0,R]`.  Overlap identification with an already-existing
preterminal solution is naturally pointwise in time: for a target elapsed time
`τ`, one wants to compare only on `[0,τ]`.

This file proves that the canonical selected path is consistent under such
restriction.

For every

    0 < τ ≤ R,

we restrict the canonical physical extension to `[0,τ]`.  The restricted path

* remains in the same `2A` Picard ball;
* satisfies the `τ` heat--Leray mild equation.

The second point is where `DuhamelLocality` is used: the full-radius extension
and the shorter normalized extension agree throughout every integration
interval `[0,q] ⊆ [0,τ]`, so their Duhamel values at `q` are identical.

The already-proved physical overlap uniqueness theorem then identifies the
normalized restriction with the Banach-selected solution constructed directly
at lifespan `τ`.

This is the semigroup-consistency bridge needed to apply uniqueness separately
at every time in the preterminal/restart overlap.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Restrict the canonical-radius physical extension to a shorter physical
interval `[0,τ]`. -/
noncomputable def h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
    {ν A τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (_hτ : 0 ≤ τ) :
    H3SpectralPhysicalVelocityPath τ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q : Set.Icc (0 : ℝ) τ =>
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ (q : ℝ))
    (by
      unfold
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      unfold
        h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      exact
        (continuous_h3PathPhysicalRealExtension
          (h3FinHeatLerayRestartRadius ν A)
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadius
            hν U₀ hA hU₀)).comp
          continuous_subtype_val)
    (2 * A)
    (by
      intro q
      have hPathNorm :
          ‖h3SpectralFinHeatLerayMildSolutionAtRestartRadius
              hν U₀ hA hU₀‖
            ≤
          2 * A := by
        apply
          (BoundedContinuousFunction.norm_le
            (f :=
              h3SpectralFinHeatLerayMildSolutionAtRestartRadius
                hν U₀ hA hU₀)
            (by linarith [hA])).2
        intro s
        exact
          norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_apply_le_twoA
            hν U₀ hA hU₀ s

      unfold
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      unfold
        h3SpectralFinHeatLerayMildSolutionPhysicalExtension

      exact
        (norm_h3PathPhysicalRealExtension_le
          (h3FinHeatLerayRestartRadius ν A)
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadius
            hν U₀ hA hU₀)
          (q : ℝ)).trans hPathNorm)

/-- Evaluation of the restricted physical path is literally evaluation of the
canonical-radius physical extension. -/
@[simp]
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical_apply
    {ν A τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hτ : 0 ≤ τ)
    (q : Set.Icc (0 : ℝ) τ) :
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
        hν U₀ hA hU₀ hτ q
      =
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀ (q : ℝ) :=
  rfl

/-- Every slice of the restricted canonical path remains in the original
`2A` Picard ball. -/
theorem norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical_apply_le_twoA
    {ν A τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hτ : 0 ≤ τ)
    (q : Set.Icc (0 : ℝ) τ) :
    ‖h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
        hν U₀ hA hU₀ hτ q‖
      ≤
    2 * A := by
  have hPathNorm :
      ‖h3SpectralFinHeatLerayMildSolutionAtRestartRadius
          hν U₀ hA hU₀‖
        ≤
      2 * A := by
    apply
      (BoundedContinuousFunction.norm_le
        (f :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadius
            hν U₀ hA hU₀)
        (by linarith [hA])).2
    intro s
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_apply_le_twoA
        hν U₀ hA hU₀ s

  rw [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical_apply
  ]

  unfold
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
  unfold
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension

  exact
    (norm_h3PathPhysicalRealExtension_le
      (h3FinHeatLerayRestartRadius ν A)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius
        hν U₀ hA hU₀)
      (q : ℝ)).trans hPathNorm

/-- The canonical smallness inequality descends to every shorter nonnegative
lifespan. -/
theorem h3FinHeatLerayRestartRadius_smallness_of_le
    {ν A τ : ℝ}
    (hA : 0 < A)
    (_hτ : 0 ≤ τ)
    (hτR : τ ≤ h3FinHeatLerayRestartRadius ν A) :
    8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ
      ≤
    1 := by
  have hCoeff :
      0 ≤
        8 * h3HeatLerayDuhamelPathCoefficient ν * A := by
    exact
      mul_nonneg
        (mul_nonneg
          (by norm_num)
          (h3HeatLerayDuhamelPathCoefficient_nonneg ν))
        hA.le

  calc
    8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ
        ≤
      8 * h3HeatLerayDuhamelPathCoefficient ν * A *
        Real.sqrt (h3FinHeatLerayRestartRadius ν A) := by
          exact
            mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt hτR)
              hCoeff
    _ ≤ 1 :=
      h3FinHeatLerayRestartRadius_smallness
        ν hA.le

/-- The restriction of the radius solution satisfies the shorter physical
heat--Leray mild equation. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical_satisfies_mild
    {ν A τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hτ : 0 < τ)
    (hτR : τ ≤ h3FinHeatLerayRestartRadius ν A)
    (s : H3UnitTime) :
    h3SpectralVelocityHeatApplyNN
        ν hν.le
        (h3PhysicalTimeNN τ hτ.le s)
        U₀
      +
    h3SpectralFinHeatLerayDuhamel
        ν
        (h3PhysicalTime τ s)
        hν
        (h3PathPhysicalRealExtension
          τ
          (h3SpectralNormalizedPathOfPhysical
            hτ.le
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
              hν U₀ hA hU₀ hτ.le)))
        (h3PathPhysicalRealExtension
          τ
          (h3SpectralNormalizedPathOfPhysical
            hτ.le
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
              hν U₀ hA hU₀ hτ.le)))
      =
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
      hν U₀ hA hU₀ hτ.le
      (h3PhysicalTimeMap τ hτ.le s) := by
  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralVelocityState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let P : H3SpectralPhysicalVelocityPath τ :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
      hν U₀ hA hU₀ hτ.le

  let V : ℝ → H3SpectralVelocityState :=
    h3PathPhysicalRealExtension
      τ
      (h3SpectralNormalizedPathOfPhysical hτ.le P)

  let qR : Set.Icc (0 : ℝ) R :=
    ⟨
      h3PhysicalTime τ s,
      (h3PhysicalTime_mem_Icc hτ.le s).1,
      le_trans
        (h3PhysicalTime_mem_Icc hτ.le s).2
        hτR
    ⟩

  have hSelected :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      qR

  have hNN :
      h3PhysicalTimePointNN qR
        =
      h3PhysicalTimeNN τ hτ.le s := by
    apply Subtype.ext
    rfl

  have hqNonneg :
      0 ≤ h3PhysicalTime τ s :=
    (h3PhysicalTime_mem_Icc hτ.le s).1

  have hWV :
      ∀ r : ℝ,
        r ∈ Set.Icc (0 : ℝ) (h3PhysicalTime τ s) →
          W r = V r := by
    intro r hr

    have hrτ :
        r ∈ Set.Icc (0 : ℝ) τ := by
      exact
        ⟨
          hr.1,
          le_trans
            hr.2
            (h3PhysicalTime_mem_Icc hτ.le s).2
        ⟩

    let rτ : Set.Icc (0 : ℝ) τ :=
      ⟨r, hrτ⟩

    have hRecover :=
      h3PathPhysicalRealExtension_normalizedPhysical_apply
        hτ P rτ

    have hP :
        P rτ = W r := by
      rfl

    have hV :
        V r = P rτ := by
      simpa only [V, rτ] using hRecover

    exact
      hP.symm.trans hV.symm

  have hDuhamel :
      h3SpectralFinHeatLerayDuhamel
          ν
          (h3PhysicalTime τ s)
          hν
          W W
        =
      h3SpectralFinHeatLerayDuhamel
          ν
          (h3PhysicalTime τ s)
          hν
          V V :=
    h3SpectralFinHeatLerayDuhamel_self_congr_Icc
      hν hqNonneg hWV

  rw [hNN] at hSelected

  change
    h3SpectralVelocityHeatApplyNN
        ν hν.le
        (h3PhysicalTimeNN τ hτ.le s)
        U₀
      +
    h3SpectralFinHeatLerayDuhamel
        ν
        (h3PhysicalTime τ s)
        hν
        W W
      =
    W (h3PhysicalTime τ s)
    at hSelected

  change
    h3SpectralVelocityHeatApplyNN
        ν hν.le
        (h3PhysicalTimeNN τ hτ.le s)
        U₀
      +
    h3SpectralFinHeatLerayDuhamel
        ν
        (h3PhysicalTime τ s)
        hν
        V V
      =
    P (h3PhysicalTimeMap τ hτ.le s)

  rw [← hDuhamel]

  calc
    h3SpectralVelocityHeatApplyNN
          ν hν.le
          (h3PhysicalTimeNN τ hτ.le s)
          U₀
        +
      h3SpectralFinHeatLerayDuhamel
          ν
          (h3PhysicalTime τ s)
          hν
          W W
        =
      W (h3PhysicalTime τ s) :=
        hSelected
    _ =
      P (h3PhysicalTimeMap τ hτ.le s) := by
        rfl

/-- The normalized restriction of the canonical-radius solution to any shorter
positive lifespan is exactly the Banach-selected solution constructed directly
at that lifespan. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_normalized_restrict_eq
    {ν A τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hτ : 0 < τ)
    (hτR : τ ≤ h3FinHeatLerayRestartRadius ν A) :
    h3SpectralNormalizedPathOfPhysical
        hτ.le
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
          hν U₀ hA hU₀ hτ.le)
      =
    h3SpectralFinHeatLerayMildSolution
      hν
      hτ.le
      U₀
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness_of_le
        hA hτ.le hτR) := by
  apply
    h3SpectralFinHeatLerayPhysicalOverlap_normalized_unique
      hν
      hτ.le
      U₀
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness_of_le
        hA hτ.le hτR)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical
        hν U₀ hA hU₀ hτ.le)

  · intro q

    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical_apply_le_twoA
        hν U₀ hA hU₀ hτ.le q

  · intro s

    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRestrictPhysical_satisfies_mild
        hν U₀ hA hU₀ hτ hτR s

end
end Euclidean
end Bridge
end PrimeTensor
