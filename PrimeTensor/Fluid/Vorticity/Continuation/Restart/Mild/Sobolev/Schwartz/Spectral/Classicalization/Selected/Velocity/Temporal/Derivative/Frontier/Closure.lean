import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Temporal.Derivative.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Temporal.Derivative.Reduction
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Classicalization: closure of the selected temporal derivative frontier

The selected real restart velocity now has temporal derivative regularity on the
whole strict relative restart interval `(0,R)`.

The remaining frontier predicate is written in absolute time, using the path

    s ↦ selectedVelocity (s - t)

on `(t,t+R)`.

This file closes that frontier directly.  We convert the relative derivative
criterion to `ContDiffOn ℝ 1`, compose with the affine translation
`s ↦ s - t`, and convert back to the exact derivative criterion used by
`H3PreterminalTailUnitViscositySelectedVelocityTemporalDerivativeRegularity`.

No new proposition, estimate, or analytic assumption is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityTemporalDerivativeFrontierClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected temporal derivative frontier is discharged by the canonical
restart construction itself. -/
theorem h3PreterminalTailUnitViscositySelectedVelocityTemporalDerivativeRegularity_closed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalTailUnitViscositySelectedVelocityTemporalDerivativeRegularity
      hNS ht hE hTail := by
  intro x j
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  let f₀ : ℝ → ℝ :=
    fun r : ℝ =>
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        (one_pos : (0 : ℝ) < 1)
        U₀
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        r
        x).component j

  let I₀ : Set ℝ :=
    Set.Ioo 0 R

  let shift : ℝ → ℝ :=
    fun s : ℝ => s - t

  let I : Set ℝ :=
    Set.Ioo t (t + R)

  have hRelative :
      DifferentiableOn ℝ f₀ I₀
        ∧
      ContinuousOn (deriv f₀) I₀ := by
    dsimp only [f₀, I₀, R, U₀]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        x j

  have hRelativeCriterion :
      ContDiffOn ℝ 1 f₀ I₀
        ↔
      DifferentiableOn ℝ f₀ I₀
        ∧
      ContinuousOn (deriv f₀) I₀ := by
    simpa using
      (contDiffOn_succ_iff_deriv_of_isOpen
        (𝕜 := ℝ)
        (f := f₀)
        (s := I₀)
        (n := 0)
        isOpen_Ioo)

  have hRelativeC1 :
      ContDiffOn ℝ 1 f₀ I₀ :=
    hRelativeCriterion.2 hRelative

  have hShift :
      ContDiffOn ℝ 1 shift I := by
    have hShiftGlobal :
        ContDiff ℝ 1 shift := by
      dsimp only [shift]
      fun_prop
    exact hShiftGlobal.contDiffOn

  have hMaps :
      MapsTo shift I I₀ := by
    intro s hs
    change s ∈ Set.Ioo t (t + R) at hs
    change s - t ∈ Set.Ioo 0 R
    constructor
    · exact sub_pos.mpr hs.1
    · apply (sub_lt_iff_lt_add).2
      simpa only [add_comm] using hs.2

  have hAbsoluteC1 :
      ContDiffOn ℝ 1
        (f₀ ∘ shift)
        I :=
    hRelativeC1.comp hShift hMaps

  have hAbsoluteCriterion :
      ContDiffOn ℝ 1
          (f₀ ∘ shift)
          I
        ↔
      DifferentiableOn ℝ
          (f₀ ∘ shift)
          I
        ∧
      ContinuousOn
          (deriv (f₀ ∘ shift))
          I := by
    simpa using
      (contDiffOn_succ_iff_deriv_of_isOpen
        (𝕜 := ℝ)
        (f := f₀ ∘ shift)
        (s := I)
        (n := 0)
        isOpen_Ioo)

  have hAbsolute :
      DifferentiableOn ℝ
          (f₀ ∘ shift)
          I
        ∧
      ContinuousOn
          (deriv (f₀ ∘ shift))
          I :=
    hAbsoluteCriterion.1 hAbsoluteC1

  let fAbs : ℝ → ℝ :=
    fun s : ℝ =>
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        (s - t)
        x).component j

  have hPathEq :
      (f₀ ∘ shift) = fAbs := by
    funext s
    rfl

  rw [hPathEq] at hAbsolute

  simpa only [
    fAbs,
    I,
    R
  ] using hAbsolute

end

end Euclidean
end Bridge
end PrimeTensor
