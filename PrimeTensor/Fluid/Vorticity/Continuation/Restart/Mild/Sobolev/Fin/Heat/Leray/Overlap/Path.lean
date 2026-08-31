import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Overlap.Uniqueness

/-!
# Physical-path overlap identification for the finite H³ heat--Leray restart

`FinHeatLerayOverlapUniqueness` proves uniqueness on the normalized path space
`[0,1]`.  An already-existing solution, however, is naturally presented on a
physical interval `[0,τ]`.

This file closes that packaging gap.

For a bounded continuous physical spectral path

    P : C_b([0,τ], H³_spectral),

we precompose with the physical-time map `s ↦ τ s` to obtain a normalized
path.  The normalization preserves every pointwise uniform bound.  If the
physical path satisfies the same heat--Leray mild equation along the image of
normalized time, the normalized path is therefore the Banach-selected mild
path by the already-proved overlap uniqueness theorem.

The final theorem is deliberately stated for an arbitrary physical spectral
path.  The only remaining PDE-side obligation is to construct this `P` from
the old preterminal Navier--Stokes solution and prove its restarted mild
identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Normalize a physical spectral path -/

/--
Restrict a physical-time spectral path on `[0,τ]` to normalized time
`s ∈ [0,1]` by evaluating it at physical time `τ s`.
-/
noncomputable def h3SpectralNormalizedPathOfPhysical
    {τ : ℝ}
    (hτ : 0 ≤ τ)
    (P : H3SpectralPhysicalVelocityPath τ) :
    H3SpectralVelocityPath :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s : H3UnitTime =>
      P (h3PhysicalTimeMap τ hτ s))
    (by
      exact
        P.continuous.comp
          (by
            unfold h3PhysicalTimeMap h3PhysicalTime
            fun_prop))
    ‖P‖
    (fun s =>
      BoundedContinuousFunction.norm_coe_le_norm
        P (h3PhysicalTimeMap τ hτ s))

@[simp]
theorem h3SpectralNormalizedPathOfPhysical_apply
    {τ : ℝ}
    (hτ : 0 ≤ τ)
    (P : H3SpectralPhysicalVelocityPath τ)
    (s : H3UnitTime) :
    h3SpectralNormalizedPathOfPhysical hτ P s
      =
    P (h3PhysicalTimeMap τ hτ s) :=
  rfl

/-- Normalization cannot increase the uniform norm. -/
theorem norm_h3SpectralNormalizedPathOfPhysical_le
    {τ : ℝ}
    (hτ : 0 ≤ τ)
    (P : H3SpectralPhysicalVelocityPath τ) :
    ‖h3SpectralNormalizedPathOfPhysical hτ P‖ ≤ ‖P‖ := by
  apply
    (BoundedContinuousFunction.norm_le
      (f := h3SpectralNormalizedPathOfPhysical hτ P)
      (norm_nonneg P)).2
  intro s
  exact
    BoundedContinuousFunction.norm_coe_le_norm
      P (h3PhysicalTimeMap τ hτ s)

/-- Any pointwise bound on the physical path passes to its normalized path. -/
theorem norm_h3SpectralNormalizedPathOfPhysical_le_of_forall
    {τ M : ℝ}
    (hτ : 0 ≤ τ)
    (hM : 0 ≤ M)
    (P : H3SpectralPhysicalVelocityPath τ)
    (hP : ∀ q : Set.Icc (0 : ℝ) τ, ‖P q‖ ≤ M) :
    ‖h3SpectralNormalizedPathOfPhysical hτ P‖ ≤ M := by
  apply
    (BoundedContinuousFunction.norm_le
      (f := h3SpectralNormalizedPathOfPhysical hτ P)
      hM).2
  intro s
  exact hP (h3PhysicalTimeMap τ hτ s)

/-! ## Recover the physical path on a positive interval -/

/--
For positive `τ`, extending the normalized physical path back to physical time
recovers the original path at every `q ∈ [0,τ]`.
-/
theorem h3PathPhysicalRealExtension_normalizedPhysical_apply
    {τ : ℝ}
    (hτ : 0 < τ)
    (P : H3SpectralPhysicalVelocityPath τ)
    (q : Set.Icc (0 : ℝ) τ) :
    h3PathPhysicalRealExtension
        τ
        (h3SpectralNormalizedPathOfPhysical hτ.le P)
        (q : ℝ)
      =
    P q := by
  unfold h3PathPhysicalRealExtension
  unfold h3PathRealExtension
  change
    P
        (h3PhysicalTimeMap
          τ hτ.le
          (h3ClampUnitTime ((q : ℝ) / τ)))
      =
    P q
  congr 1
  apply Subtype.ext
  exact h3PhysicalTime_clamp_div hτ.le q

/-! ## Physical overlap uniqueness -/

/--
A physical spectral path in the `2A` ball which satisfies the same restarted
heat--Leray mild equation is the canonical Banach-selected mild path after
normalization.

The mild hypothesis is written at `q = τ s`; this is exactly the form produced
by normalizing a physical overlap interval.
-/
theorem h3SpectralFinHeatLerayPhysicalOverlap_normalized_unique
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (P : H3SpectralPhysicalVelocityPath τ)
    (hPbound :
      ∀ q : Set.Icc (0 : ℝ) τ,
        ‖P q‖ ≤ 2 * A)
    (hPmild :
      ∀ s : H3UnitTime,
        h3SpectralVelocityHeatApplyNN
            ν hν.le (h3PhysicalTimeNN τ hτ s) U₀
          -
        h3SpectralFinHeatLerayDuhamel
            ν
            (h3PhysicalTime τ s)
            hν
            (h3PathPhysicalRealExtension
              τ (h3SpectralNormalizedPathOfPhysical hτ P))
            (h3PathPhysicalRealExtension
              τ (h3SpectralNormalizedPathOfPhysical hτ P))
          =
        P (h3PhysicalTimeMap τ hτ s)) :
    h3SpectralNormalizedPathOfPhysical hτ P
      =
    h3SpectralFinHeatLerayMildSolution
      hν hτ U₀ hA hU₀ hsmall := by
  let V : H3SpectralVelocityPath :=
    h3SpectralNormalizedPathOfPhysical hτ P

  have hVbound : ‖V‖ ≤ 2 * A := by
    apply
      norm_h3SpectralNormalizedPathOfPhysical_le_of_forall
        hτ
        (by linarith [hA])
        P
    exact hPbound

  have hVmild :
      h3SpectralVelocityHeatFreePath ν τ hν.le hτ U₀
          -
        h3SpectralFinHeatLerayDuhamelPathOperator hν hτ V V
        =
      V := by
    apply BoundedContinuousFunction.ext
    intro s
    have hs := hPmild s
    change
      h3SpectralVelocityHeatFreePath ν τ hν.le hτ U₀ s
        -
      h3SpectralFinHeatLerayDuhamelPathOperator hν hτ V V s
        =
      V s
    rw [h3SpectralVelocityHeatFreePath_apply]
    rw [h3SpectralFinHeatLerayDuhamelPathOperator_apply]
    change
      h3SpectralVelocityHeatApplyNN
          ν hν.le (h3PhysicalTimeNN τ hτ s) U₀
        -
      h3SpectralFinHeatLerayDuhamel
          ν
          (h3PhysicalTimeNN τ hτ s : ℝ)
          hν
          (h3PathPhysicalRealExtension τ V)
          (h3PathPhysicalRealExtension τ V)
        =
      V s
    simpa only [
      V,
      h3PhysicalTimeNN_val,
      h3SpectralNormalizedPathOfPhysical_apply
    ] using hs

  exact
    h3SpectralFinHeatLerayMildSolution_unique
      hν hτ U₀ hA hU₀ hsmall
      V hVbound hVmild

/--
Canonical-radius form of physical overlap uniqueness.  No small-time proof
argument remains.
-/
theorem h3SpectralFinHeatLerayPhysicalOverlapAtRestartRadius_normalized_unique
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (P :
      H3SpectralPhysicalVelocityPath
        (h3FinHeatLerayRestartRadius ν A))
    (hPbound :
      ∀ q : Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A),
        ‖P q‖ ≤ 2 * A)
    (hPmild :
      ∀ s : H3UnitTime,
        h3SpectralVelocityHeatApplyNN
            ν hν.le
            (h3PhysicalTimeNN
              (h3FinHeatLerayRestartRadius ν A)
              (h3FinHeatLerayRestartRadius_pos ν hA).le
              s)
            U₀
          -
        h3SpectralFinHeatLerayDuhamel
            ν
            (h3PhysicalTime
              (h3FinHeatLerayRestartRadius ν A) s)
            hν
            (h3PathPhysicalRealExtension
              (h3FinHeatLerayRestartRadius ν A)
              (h3SpectralNormalizedPathOfPhysical
                (h3FinHeatLerayRestartRadius_pos ν hA).le P))
            (h3PathPhysicalRealExtension
              (h3FinHeatLerayRestartRadius ν A)
              (h3SpectralNormalizedPathOfPhysical
                (h3FinHeatLerayRestartRadius_pos ν hA).le P))
          =
        P
          (h3PhysicalTimeMap
            (h3FinHeatLerayRestartRadius ν A)
            (h3FinHeatLerayRestartRadius_pos ν hA).le
            s)) :
    h3SpectralNormalizedPathOfPhysical
        (h3FinHeatLerayRestartRadius_pos ν hA).le P
      =
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius
      hν U₀ hA hU₀ := by
  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadius
  exact
    h3SpectralFinHeatLerayPhysicalOverlap_normalized_unique
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      P hPbound hPmild

end

end Euclidean
end Bridge
end PrimeTensor
