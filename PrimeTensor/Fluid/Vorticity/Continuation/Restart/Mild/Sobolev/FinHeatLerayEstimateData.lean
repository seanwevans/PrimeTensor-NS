import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayPathAlgebra

/-!
# Concrete heat--Leray estimate data on the spectral H³ path space

The concrete normalized Duhamel path operator is currently stated for a
nonnegative physical lifespan, while `H3HeatLerayEstimateData` asks for a
bilinear operator defined for every real parameter and only assumes
nonnegativity when requesting the norm estimate.

We bridge that small interface mismatch by totalizing the concrete operator:
for a negative lifespan it is zero, and for a nonnegative lifespan it is the
actual finite heat--Leray operator.  This preserves the exact operator on every
physical time window used by the Picard argument.

With that totalization in hand, the already-green ingredients fit the abstract
estimate-data structure directly:

* the free term is the normalized spectral heat path;
* `A` is any positive bound for the restart state;
* `C` is `h3HeatLerayDuhamelPathCoefficient ν`;
* the `sqrt τ` estimate comes from `FinHeatLerayPathOperator`;
* the diagonal subtraction law comes from `FinHeatLerayPathAlgebra`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Totalized concrete Duhamel path operator -/

/--
Total real-parameter version of the concrete finite heat--Leray path operator.
It agrees with the physical operator for nonnegative lifespan and is zero for
negative lifespan.
-/
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

/-- On a physical nonnegative lifespan, totalization is invisible. -/
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

/-- The totalized operator inherits the concrete `sqrt τ` estimate. -/
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

/--
The totalized operator satisfies the Picard diagonal subtraction identity for
all real parameters.
-/
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

/-! ## Concrete abstract estimate package -/

/--
Concrete `H3HeatLerayEstimateData` for a restart state `U₀` and target physical
lifespan `τ₀`.

The free heat path is formed on `τ₀`; the Duhamel family remains parameterized
by its real lifespan as required by the abstract estimate interface.  When the
resulting Picard problem is instantiated at `τ₀`, both pieces therefore use the
same physical window.
-/
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
    h3SpectralFinHeatLerayDuhamelPathOperatorTotal hν
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
      norm_h3SpectralFinHeatLerayDuhamelPathOperatorTotal_le
        hν hτ U V
  diagonal_sub := by
    intro τ U V
    exact
      h3SpectralFinHeatLerayDuhamelPathOperatorTotal_diagonal_sub
        hν τ U V

end

end Euclidean
end Bridge
end PrimeTensor
