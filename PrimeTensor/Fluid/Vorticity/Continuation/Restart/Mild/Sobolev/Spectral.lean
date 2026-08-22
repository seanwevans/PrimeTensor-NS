import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path

/-!
# Weighted Fourier H³ solver state

The 120-coordinate `H3L2JetState` is the right object for exact derivative
energy bookkeeping, but an arbitrary element of that product need not be the
derivative jet of one underlying velocity field.  In particular, treating an
arbitrary jet as the nonlinear solver state would not justify Sobolev
multiplication.

This file therefore introduces a second, complementary representation:

* the **jet state** remains the exact H³ energy observable;
* the **spectral state** is the Banach solver state.

For one scalar field, let

    q(ξ) = (2π)² |ξ|²

and define the exact ordered-derivative weight-square

    W₃(ξ)² = 1 + q(ξ) + q(ξ)² + q(ξ)³.

Indeed, under Plancherel the ordered first-, second-, and third-derivative
families contribute `q`, `q²`, and `q³`, respectively.

A scalar spectral H³ state stores the weighted Fourier amplitude

    G(ξ) = W₃(ξ) * f̂(ξ)

as an ordinary complex `L²` element.  Hence the state space is complete by
construction.  Heat evolution remains diagonal on `G`, since the Sobolev
weight commutes with the scalar heat multiplier.

The exact Plancherel bridge from the existing derivative-jet energy to this
spectral norm is intentionally left to the next bridge file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SpectralSobolev
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact H³ spectral weight -/

/-- `q(ξ) = (2π)² |ξ|²`, the Fourier square-gradient factor. -/
def h3FourierGradientSquare
    (ξ : H3FourierPoint3) : ℝ :=
  (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2

/--
Square of the exact ordered-derivative H³ Fourier weight:

`1 + q + q² + q³`.
-/
def h3SobolevFrequencyWeightSq
    (ξ : H3FourierPoint3) : ℝ :=
  1
    + h3FourierGradientSquare ξ
    + (h3FourierGradientSquare ξ) ^ 2
    + (h3FourierGradientSquare ξ) ^ 3

/-- The gradient-square frequency factor is nonnegative. -/
theorem h3FourierGradientSquare_nonneg
    (ξ : H3FourierPoint3) :
    0 ≤ h3FourierGradientSquare ξ := by
  unfold h3FourierGradientSquare
  positivity

/-- The H³ weight-square is at least one. -/
theorem one_le_h3SobolevFrequencyWeightSq
    (ξ : H3FourierPoint3) :
    1 ≤ h3SobolevFrequencyWeightSq ξ := by
  have hq : 0 ≤ h3FourierGradientSquare ξ :=
    h3FourierGradientSquare_nonneg ξ
  have hq2 : 0 ≤ (h3FourierGradientSquare ξ) ^ 2 := by
    positivity
  have hq3 : 0 ≤ (h3FourierGradientSquare ξ) ^ 3 := by
    positivity
  unfold h3SobolevFrequencyWeightSq
  linarith

/-- The exact H³ Fourier weight itself. -/
def h3SobolevFrequencyWeight
    (ξ : H3FourierPoint3) : ℝ :=
  Real.sqrt (h3SobolevFrequencyWeightSq ξ)

/-- The H³ Fourier weight is at least one. -/
theorem one_le_h3SobolevFrequencyWeight
    (ξ : H3FourierPoint3) :
    1 ≤ h3SobolevFrequencyWeight ξ := by
  unfold h3SobolevFrequencyWeight
  simpa using
    (Real.sqrt_le_sqrt
      (one_le_h3SobolevFrequencyWeightSq ξ))

/-- In particular, the H³ Fourier weight is strictly positive. -/
theorem h3SobolevFrequencyWeight_pos
    (ξ : H3FourierPoint3) :
    0 < h3SobolevFrequencyWeight ξ :=
  lt_of_lt_of_le zero_lt_one
    (one_le_h3SobolevFrequencyWeight ξ)

/-- The polynomial weight-square is continuous in frequency. -/
theorem continuous_h3SobolevFrequencyWeightSq :
    Continuous h3SobolevFrequencyWeightSq := by
  unfold h3SobolevFrequencyWeightSq h3FourierGradientSquare
  fun_prop

/-- The H³ Fourier weight is continuous in frequency. -/
theorem continuous_h3SobolevFrequencyWeight :
    Continuous h3SobolevFrequencyWeight := by
  unfold h3SobolevFrequencyWeight
  exact
    Real.continuous_sqrt.comp
      continuous_h3SobolevFrequencyWeightSq

/-! ## Complete weighted Fourier solver state -/

/--
One scalar H³ solver state.

An element is interpreted as the **weighted** Fourier amplitude
`W₃ * f̂`, not as the raw Fourier transform.
-/
abbrev H3SpectralScalarState : Type :=
  H3FourierComplexL2

/--
Three-component velocity H³ solver state.

The finite product uses the project-wide sup norm; this is equivalent to the
usual finite-component Hilbert norm and is convenient for the existing Picard
bookkeeping.
-/
abbrev H3SpectralVelocityState : Type :=
  Fin 3 → H3SpectralScalarState

/-- Normalized continuous mild path in the spectral H³ velocity state. -/
abbrev H3SpectralVelocityPath : Type :=
  H3Path H3SpectralVelocityState

/-- Scalar weighted Fourier H³ state is complete. -/
theorem h3SpectralScalarState_complete :
    CompleteSpace H3SpectralScalarState := by
  infer_instance

/-- Three-component weighted Fourier H³ velocity state is complete. -/
theorem h3SpectralVelocityState_complete :
    CompleteSpace H3SpectralVelocityState := by
  infer_instance

/-- The normalized spectral H³ velocity path space is complete. -/
theorem h3SpectralVelocityPath_complete :
    CompleteSpace H3SpectralVelocityPath := by
  infer_instance

/-- Every velocity component is controlled by the finite-product state norm. -/
theorem h3SpectralVelocity_coordinate_norm_le
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    ‖U j‖ ≤ ‖U‖ := by
  exact
    (pi_norm_le_iff_of_nonneg (norm_nonneg U)).1
      le_rfl j

/-! ## Heat evolution on the weighted solver state -/

/--
Heat evolution of one weighted scalar Fourier amplitude.

Because the H³ weight and heat symbol are both scalar Fourier multipliers,
the heat action on `W₃ f̂` is exactly the same multiplier already constructed
in `Heat.Path`.
-/
def h3SpectralScalarHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (G : H3SpectralScalarState) :
    H3SpectralScalarState :=
  h3HeatFrequencyApplyNN ν hν t G

/-- Heat evolution of a three-component spectral H³ velocity state. -/
def h3SpectralVelocityHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralVelocityState) :
    H3SpectralVelocityState :=
  fun j =>
    h3SpectralScalarHeatApplyNN ν hν t (U j)

@[simp]
theorem h3SpectralVelocityHeatApplyNN_apply
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    h3SpectralVelocityHeatApplyNN ν hν t U j =
      h3SpectralScalarHeatApplyNN ν hν t (U j) :=
  rfl

/-- Scalar weighted Fourier heat evolution is contractive. -/
theorem norm_h3SpectralScalarHeatApplyNN_le
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarHeatApplyNN ν hν t G‖ ≤ ‖G‖ := by
  unfold h3SpectralScalarHeatApplyNN h3HeatFrequencyApplyNN
  exact
    norm_h3HeatFrequencyApply_le
      hν t.property G

/-- Three-component weighted Fourier heat evolution is contractive. -/
theorem norm_h3SpectralVelocityHeatApplyNN_le
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatApplyNN ν hν t U‖ ≤ ‖U‖ := by
  apply
    (pi_norm_le_iff_of_nonneg (norm_nonneg U)).2
  intro j
  calc
    ‖h3SpectralVelocityHeatApplyNN ν hν t U j‖
        ≤ ‖U j‖ :=
      norm_h3SpectralScalarHeatApplyNN_le
        ν hν t (U j)
    _ ≤ ‖U‖ :=
      h3SpectralVelocity_coordinate_norm_le U j

/-- Strong continuity of scalar weighted Fourier heat evolution. -/
theorem continuous_h3SpectralScalarHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (G : H3SpectralScalarState) :
    Continuous
      (fun t : ℝ≥0 =>
        h3SpectralScalarHeatApplyNN ν hν t G) := by
  exact
    continuous_h3HeatFrequencyApplyNN ν hν G

/-- Strong continuity of three-component spectral H³ heat evolution. -/
theorem continuous_h3SpectralVelocityHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralVelocityState) :
    Continuous
      (fun t : ℝ≥0 =>
        h3SpectralVelocityHeatApplyNN ν hν t U) := by
  apply continuous_pi
  intro j
  exact
    continuous_h3SpectralScalarHeatApplyNN
      ν hν (U j)

/-! ## Genuine free mild path in the spectral H³ state -/

/--
Normalized free heat path in the weighted Fourier H³ velocity solver state:

` s ↦ exp (ν τ s Δ) U₀ `.
-/
def h3SpectralVelocityHeatFreePath
    (ν τ : ℝ)
    (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ)
    (U : H3SpectralVelocityState) :
    H3SpectralVelocityPath :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s : H3UnitTime =>
      h3SpectralVelocityHeatApplyNN
        ν hν (h3PhysicalTimeNN τ hτ s) U)
    ((continuous_h3SpectralVelocityHeatApplyNN ν hν U).comp
      (continuous_h3PhysicalTimeNN τ hτ))
    ‖U‖
    (fun s =>
      norm_h3SpectralVelocityHeatApplyNN_le
        ν hν (h3PhysicalTimeNN τ hτ s) U)

@[simp]
theorem h3SpectralVelocityHeatFreePath_apply
    (ν τ : ℝ)
    (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ)
    (U : H3SpectralVelocityState)
    (s : H3UnitTime) :
    h3SpectralVelocityHeatFreePath ν τ hν hτ U s =
      h3SpectralVelocityHeatApplyNN
        ν hν (h3PhysicalTimeNN τ hτ s) U :=
  rfl

/-- The spectral free path has no larger norm than its initial H³ state. -/
theorem norm_h3SpectralVelocityHeatFreePath_le
    (ν τ : ℝ)
    (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ)
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatFreePath ν τ hν hτ U‖ ≤ ‖U‖ := by
  apply
    (BoundedContinuousFunction.norm_le
      (f := h3SpectralVelocityHeatFreePath ν τ hν hτ U)
      (norm_nonneg U)).2
  intro s
  exact
    norm_h3SpectralVelocityHeatApplyNN_le
      ν hν (h3PhysicalTimeNN τ hτ s) U

end

end Euclidean
end Bridge
end PrimeTensor
