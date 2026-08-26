import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Picard.Solution

/-!
# Physical-time spectral heat--Leray mild solution

The Banach fixed point is constructed on the normalized interval `[0,1]`.
This file restricts its already-defined global physical-time extension to the
actual interval `[0,τ]`.

No inverse Fourier decoder is introduced here: the state remains the honest
weighted spectral H³ velocity state.  The result is nevertheless a genuine
continuous path indexed by physical time, with the same `2A` bound and the
concrete heat--Leray mild equation at every physical time in the restart
window.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-- A bounded continuous spectral H³ velocity path on the physical interval `[0,τ]`. -/
abbrev H3SpectralPhysicalVelocityPath (τ : ℝ) : Type :=
  BoundedContinuousFunction (Set.Icc (0 : ℝ) τ) H3SpectralVelocityState

/-- A point of the physical interval, viewed as a nonnegative real time. -/
def h3PhysicalTimePointNN
    {τ : ℝ}
    (q : Set.Icc (0 : ℝ) τ) : ℝ≥0 :=
  ⟨(q : ℝ), q.property.1⟩

@[simp]
theorem h3PhysicalTimePointNN_val
    {τ : ℝ}
    (q : Set.Icc (0 : ℝ) τ) :
    (h3PhysicalTimePointNN q : ℝ) = (q : ℝ) :=
  rfl

/--
For `q ∈ [0,τ]` with `τ ≥ 0`, clamping `q/τ` and converting back to physical
time returns `q`.  This includes the degenerate case `τ = 0`.
-/
theorem h3PhysicalTime_clamp_div
    {τ : ℝ}
    (hτ : 0 ≤ τ)
    (q : Set.Icc (0 : ℝ) τ) :
    h3PhysicalTime τ (h3ClampUnitTime ((q : ℝ) / τ)) = (q : ℝ) := by
  by_cases hzero : τ = 0
  · subst τ
    have hq : (q : ℝ) = 0 :=
      le_antisymm q.property.2 q.property.1
    simp [h3PhysicalTime, hq]
  · have hτpos : 0 < τ :=
      lt_of_le_of_ne hτ (Ne.symm hzero)
    have hdiv : (q : ℝ) / τ ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg q.property.1 hτ
      · apply (div_le_iff₀ hτpos).2
        simpa using q.property.2
    rw [h3PhysicalTime, h3ClampUnitTime_coe_of_mem_Icc hdiv]
    field_simp [hzero]

/-- Nonnegative-time form of `h3PhysicalTime_clamp_div`. -/
@[simp]
theorem h3PhysicalTimeNN_clamp_div
    {τ : ℝ}
    (hτ : 0 ≤ τ)
    (q : Set.Icc (0 : ℝ) τ) :
    h3PhysicalTimeNN τ hτ
        (h3ClampUnitTime ((q : ℝ) / τ))
      =
    h3PhysicalTimePointNN q := by
  apply Subtype.ext
  exact h3PhysicalTime_clamp_div hτ q

/-- Restrict a normalized path's canonical physical extension to `[0,τ]`. -/
noncomputable def h3SpectralPhysicalPathOfNormalized
    (τ : ℝ)
    (U : H3SpectralVelocityPath) :
    H3SpectralPhysicalVelocityPath τ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q : Set.Icc (0 : ℝ) τ =>
      h3PathPhysicalRealExtension τ U (q : ℝ))
    ((continuous_h3PathPhysicalRealExtension τ U).comp
      continuous_subtype_val)
    ‖U‖
    (fun q =>
      norm_h3PathPhysicalRealExtension_le τ U (q : ℝ))

@[simp]
theorem h3SpectralPhysicalPathOfNormalized_apply
    (τ : ℝ)
    (U : H3SpectralVelocityPath)
    (q : Set.Icc (0 : ℝ) τ) :
    h3SpectralPhysicalPathOfNormalized τ U q
      =
    h3PathPhysicalRealExtension τ U (q : ℝ) :=
  rfl

/-- The globally defined physical-time extension of the selected mild path. -/
noncomputable def h3SpectralFinHeatLerayMildSolutionPhysicalExtension
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1) :
    ℝ → H3SpectralVelocityState :=
  h3PathPhysicalRealExtension τ
    (h3SpectralFinHeatLerayMildSolution
      hν hτ U₀ hA hU₀ hsmall)

/-- The Banach-selected solution, now indexed by actual physical time `q ∈ [0,τ]`. -/
noncomputable def h3SpectralFinHeatLerayPhysicalMildSolution
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1) :
    H3SpectralPhysicalVelocityPath τ :=
  h3SpectralPhysicalPathOfNormalized τ
    (h3SpectralFinHeatLerayMildSolution
      hν hτ U₀ hA hU₀ hsmall)

@[simp]
theorem h3SpectralFinHeatLerayPhysicalMildSolution_apply
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ) :
    h3SpectralFinHeatLerayPhysicalMildSolution
        hν hτ U₀ hA hU₀ hsmall q
      =
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall (q : ℝ) := by
  rfl

/-- Every physical-time slice retains the Banach ball bound `2A`. -/
theorem norm_h3SpectralFinHeatLerayPhysicalMildSolution_apply_le_twoA
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ) :
    ‖h3SpectralFinHeatLerayPhysicalMildSolution
        hν hτ U₀ hA hU₀ hsmall q‖
      ≤ 2 * A := by
  change
    ‖h3SpectralFinHeatLerayMildSolution
        hν hτ U₀ hA hU₀ hsmall
        (h3ClampUnitTime ((q : ℝ) / τ))‖
      ≤ 2 * A
  exact
    norm_h3SpectralFinHeatLerayMildSolution_apply_le_twoA
      hν hτ U₀ hA hU₀ hsmall
      (h3ClampUnitTime ((q : ℝ) / τ))

/--
At every physical time `q ∈ [0,τ]`, the selected path satisfies the concrete
heat--Leray mild equation with the globally clamped physical-time extension as
its nonlinear input path.
-/
theorem h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ) :
    h3SpectralVelocityHeatApplyNN
        ν hν.le (h3PhysicalTimePointNN q) U₀
      +
    h3SpectralFinHeatLerayDuhamel
        ν (q : ℝ) hν
        (h3SpectralFinHeatLerayMildSolutionPhysicalExtension
          hν hτ U₀ hA hU₀ hsmall)
        (h3SpectralFinHeatLerayMildSolutionPhysicalExtension
          hν hτ U₀ hA hU₀ hsmall)
      =
    h3SpectralFinHeatLerayPhysicalMildSolution
      hν hτ U₀ hA hU₀ hsmall q := by
  have hPath :=
    h3SpectralFinHeatLerayMildSolution_satisfies_mild
      hν hτ U₀ hA hU₀ hsmall
  have hAt :=
    congrArg
      (fun P : H3SpectralVelocityPath =>
        P (h3ClampUnitTime ((q : ℝ) / τ)))
      hPath
  change
    h3SpectralVelocityHeatFreePath
        ν τ hν.le hτ U₀
        (h3ClampUnitTime ((q : ℝ) / τ))
      +
    h3SpectralFinHeatLerayDuhamelPathOperator
        hν hτ
        (h3SpectralFinHeatLerayMildSolution
          hν hτ U₀ hA hU₀ hsmall)
        (h3SpectralFinHeatLerayMildSolution
          hν hτ U₀ hA hU₀ hsmall)
        (h3ClampUnitTime ((q : ℝ) / τ))
      =
    h3SpectralFinHeatLerayMildSolution
      hν hτ U₀ hA hU₀ hsmall
      (h3ClampUnitTime ((q : ℝ) / τ)) at hAt
  rw [
    h3SpectralVelocityHeatFreePath_apply,
    h3SpectralFinHeatLerayDuhamelPathOperator_apply,
    h3PhysicalTimeNN_clamp_div hτ q
  ] at hAt
  simpa only [
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension,
    h3SpectralFinHeatLerayPhysicalMildSolution,
    h3SpectralPhysicalPathOfNormalized_apply,
    h3PhysicalTimePointNN_val,
    h3PathPhysicalRealExtension,
    h3PathRealExtension
  ] using hAt

end

end Euclidean
end Bridge
end PrimeTensor
