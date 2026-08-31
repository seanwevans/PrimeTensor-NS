import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Path.Algebra

/-!
# Concrete heat--Leray estimate data on the spectral H³ path space

The positive heat--Leray Duhamel operator is kept as a reusable analytic
object.  The Navier--Stokes mild equation, however, contains its negative:

    U(t) = H_t U₀ - ∫₀ᵗ H_{t-s} P div(U ⊗ U)(s) ds.

This file therefore inserts the sign at the Picard boundary rather than into
the positive instantaneous kernel.  All norm, smoothing, Fourier
reconstruction, and physical-closure results for the positive Duhamel object
remain unchanged.

The concrete normalized Duhamel path operator is stated for nonnegative
physical lifespan, while `H3HeatLerayEstimateData` asks for a bilinear operator
defined for every real parameter.  We first totalize the positive operator,
then negate that totalized operator to obtain the signed Navier--Stokes
nonlinearity supplied to the abstract fixed-point package.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Totalized positive Duhamel path operator -/

/-- Total real-parameter version of the positive finite heat--Leray path
operator.  It agrees with the physical operator for nonnegative lifespan and
is zero for negative lifespan. -/
noncomputable def h3SpectralFinHeatLerayDuhamelPathOperatorTotal
    {ν : ℝ}
    (hν : 0 < ν)
    (τ : ℝ)
    (U V : H3SpectralVelocityPath) :
    H3SpectralVelocityPath :=
  if hτ : 0 ≤ τ then
    h3SpectralFinHeatLerayDuhamelPathOperator hν hτ U V
  else
    0

/-- On a physical nonnegative lifespan, positive totalization is invisible. -/
@[simp]
theorem h3SpectralFinHeatLerayDuhamelPathOperatorTotal_of_nonneg
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U V : H3SpectralVelocityPath) :
    h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ U V
      =
    h3SpectralFinHeatLerayDuhamelPathOperator hν hτ U V := by
  simp [h3SpectralFinHeatLerayDuhamelPathOperatorTotal, hτ]

/-- The positive totalized operator inherits the concrete `sqrt τ` estimate. -/
theorem norm_h3SpectralFinHeatLerayDuhamelPathOperatorTotal_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U V : H3SpectralVelocityPath) :
    ‖h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ U V‖
      ≤
    h3HeatLerayDuhamelPathCoefficient ν *
      Real.sqrt τ * ‖U‖ * ‖V‖ := by
  rw [h3SpectralFinHeatLerayDuhamelPathOperatorTotal_of_nonneg hν hτ]
  exact
    norm_h3SpectralFinHeatLerayDuhamelPathOperator_le
      hν hτ U V

/-- The positive totalized operator satisfies the Picard diagonal subtraction
identity for all real parameters. -/
theorem h3SpectralFinHeatLerayDuhamelPathOperatorTotal_diagonal_sub
    {ν : ℝ}
    (hν : 0 < ν)
    (τ : ℝ)
    (U V : H3SpectralVelocityPath) :
    h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ U U
      -
    h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ V V
      =
    h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ (U - V) U
      +
    h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ V (U - V) := by
  by_cases hτ : 0 ≤ τ
  · simp only [
      h3SpectralFinHeatLerayDuhamelPathOperatorTotal_of_nonneg
        hν hτ]
    exact
      h3SpectralFinHeatLerayDuhamelPathOperator_diagonal_sub
        hν hτ U V
  · simp [h3SpectralFinHeatLerayDuhamelPathOperatorTotal, hτ]

/-! ## Signed Navier--Stokes Duhamel operator -/

/-- The nonlinear operator appearing in the Navier--Stokes mild equation:
the negative of the positive heat--Leray Duhamel operator. -/
noncomputable def h3SpectralFinNavierStokesDuhamelPathOperatorTotal
    {ν : ℝ}
    (hν : 0 < ν)
    (τ : ℝ)
    (U V : H3SpectralVelocityPath) :
    H3SpectralVelocityPath :=
  - h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ U V

/-- On a nonnegative lifespan the signed operator is exactly minus the
concrete positive Duhamel path operator. -/
@[simp]
theorem h3SpectralFinNavierStokesDuhamelPathOperatorTotal_of_nonneg
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U V : H3SpectralVelocityPath) :
    h3SpectralFinNavierStokesDuhamelPathOperatorTotal hν τ U V
      =
    - h3SpectralFinHeatLerayDuhamelPathOperator hν hτ U V := by
  unfold h3SpectralFinNavierStokesDuhamelPathOperatorTotal
  rw [h3SpectralFinHeatLerayDuhamelPathOperatorTotal_of_nonneg hν hτ]

/-- Negating the positive Duhamel operator does not change its norm bound. -/
theorem norm_h3SpectralFinNavierStokesDuhamelPathOperatorTotal_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U V : H3SpectralVelocityPath) :
    ‖h3SpectralFinNavierStokesDuhamelPathOperatorTotal hν τ U V‖
      ≤
    h3HeatLerayDuhamelPathCoefficient ν *
      Real.sqrt τ * ‖U‖ * ‖V‖ := by
  unfold h3SpectralFinNavierStokesDuhamelPathOperatorTotal
  rw [norm_neg]
  exact
    norm_h3SpectralFinHeatLerayDuhamelPathOperatorTotal_le
      hν hτ U V

/-- The signed Navier--Stokes operator inherits the same diagonal subtraction
identity. -/
theorem h3SpectralFinNavierStokesDuhamelPathOperatorTotal_diagonal_sub
    {ν : ℝ}
    (hν : 0 < ν)
    (τ : ℝ)
    (U V : H3SpectralVelocityPath) :
    h3SpectralFinNavierStokesDuhamelPathOperatorTotal hν τ U U
      -
    h3SpectralFinNavierStokesDuhamelPathOperatorTotal hν τ V V
      =
    h3SpectralFinNavierStokesDuhamelPathOperatorTotal hν τ (U - V) U
      +
    h3SpectralFinNavierStokesDuhamelPathOperatorTotal hν τ V (U - V) := by
  have h :=
    h3SpectralFinHeatLerayDuhamelPathOperatorTotal_diagonal_sub
      hν τ U V
  unfold h3SpectralFinNavierStokesDuhamelPathOperatorTotal
  rw [show
    -h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ U U
        -
      -h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ V V
      =
    -(
      h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ U U
        -
      h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν τ V V) by
        abel]
  rw [h]
  abel

/-! ## Concrete abstract estimate package -/

/-- Concrete fixed-point estimate data for the Navier--Stokes mild equation.

The positive Duhamel object remains unchanged elsewhere in the library; only
the operator supplied to Picard carries the required minus sign. -/
noncomputable def h3SpectralFinHeatLerayEstimateData
    {ν τ₀ A : ℝ}
    (hν : 0 < ν)
    (hτ₀ : 0 ≤ τ₀)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    H3HeatLerayEstimateData H3SpectralVelocityPath where
  free :=
    h3SpectralVelocityHeatFreePath
      ν τ₀ hν.le hτ₀ U₀
  duhamel :=
    h3SpectralFinNavierStokesDuhamelPathOperatorTotal hν
  A := A
  C := h3HeatLerayDuhamelPathCoefficient ν
  A_pos := hA
  C_nonneg :=
    h3HeatLerayDuhamelPathCoefficient_nonneg ν
  free_bound := by
    calc
      ‖h3SpectralVelocityHeatFreePath
          ν τ₀ hν.le hτ₀ U₀‖
          ≤ ‖U₀‖ :=
        norm_h3SpectralVelocityHeatFreePath_le
          ν τ₀ hν.le hτ₀ U₀
      _ ≤ A := hU₀
  duhamel_bound := by
    intro τ hτ U V
    exact
      norm_h3SpectralFinNavierStokesDuhamelPathOperatorTotal_le
        hν hτ U V
  diagonal_sub := by
    intro τ U V
    exact
      h3SpectralFinNavierStokesDuhamelPathOperatorTotal_diagonal_sub
        hν τ U V

end

end Euclidean
end Bridge
end PrimeTensor
