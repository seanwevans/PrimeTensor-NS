import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Difference.Energy

/-!
# Endpoint interpolation algebra for H³ spectral continuity

The remaining physical-tail continuity frontier currently asks for strong
`L²` continuity of every ordered H³ jet slot.  The middle derivative orders
are not analytically independent.

For a nonnegative radial frequency variable `r`, the full H³ polynomial weight

    1 + r + r² + r³

is controlled by the endpoint weight

    1 + r³

with the uniform constant `3`.

This is the elementary interpolation algebra needed to reduce spectral-path
continuity to the zeroth and third-order Fourier jets.  The next layer can
apply the scaled inequality pointwise to the squared norm of a Fourier
difference and integrate.

No Navier--Stokes evolution hypothesis is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- For nonnegative `r`, the linear H³ radial weight is controlled by the
zeroth-plus-third endpoint weight. -/
theorem h3_nonneg_linear_le_one_add_cube
    (r : ℝ)
    (hr : 0 ≤ r) :
    r ≤ 1 + r ^ 3 := by
  by_cases hOne : r ≤ 1
  · have hCube : 0 ≤ r ^ 3 :=
      pow_nonneg hr 3
    linarith
  · have hOneLt : 1 < r :=
      lt_of_not_ge hOne
    have hSub : 0 ≤ r - 1 :=
      sub_nonneg.mpr hOneLt.le
    have hPlus : 0 ≤ r + 1 := by
      linarith
    have hProd :
        0 ≤ r * (r - 1) * (r + 1) :=
      mul_nonneg (mul_nonneg hr hSub) hPlus
    nlinarith

/-- For nonnegative `r`, the quadratic H³ radial weight is controlled by the
zeroth-plus-third endpoint weight. -/
theorem h3_nonneg_square_le_one_add_cube
    (r : ℝ)
    (hr : 0 ≤ r) :
    r ^ 2 ≤ 1 + r ^ 3 := by
  by_cases hOne : r ≤ 1
  · have hGap : 0 ≤ 1 - r :=
      sub_nonneg.mpr hOne
    have hProd :
        0 ≤ r * (1 - r) :=
      mul_nonneg hr hGap
    nlinarith
  · have hOneLt : 1 < r :=
      lt_of_not_ge hOne
    have hSub : 0 ≤ r - 1 :=
      sub_nonneg.mpr hOneLt.le
    have hProd :
        0 ≤ (r - 1) * (r ^ 2) :=
      mul_nonneg hSub (sq_nonneg r)
    nlinarith

/-- The complete radial H³ square weight is bounded by three times the
zeroth-plus-third endpoint weight. -/
theorem h3_radial_full_weight_le_three_endpoint_weight
    (r : ℝ)
    (hr : 0 ≤ r) :
    1 + r + r ^ 2 + r ^ 3
      ≤
    3 * (1 + r ^ 3) := by
  have hLinear :=
    h3_nonneg_linear_le_one_add_cube r hr
  have hSquare :=
    h3_nonneg_square_le_one_add_cube r hr
  nlinarith

/-- Density-scaled form of the endpoint interpolation inequality.

This is the form used under a Fourier integral: `a` will be the squared norm
of the base Fourier difference, hence is nonnegative. -/
theorem h3_radial_full_weight_mul_le_three_endpoint_weight_mul
    (r a : ℝ)
    (hr : 0 ≤ r)
    (ha : 0 ≤ a) :
    a * (1 + r + r ^ 2 + r ^ 3)
      ≤
    a * (3 * (1 + r ^ 3)) := by
  exact
    mul_le_mul_of_nonneg_left
      (h3_radial_full_weight_le_three_endpoint_weight r hr)
      ha

/-- Squared complex-norm specialization of the density-scaled endpoint
interpolation inequality. -/
theorem h3_radial_complex_norm_sq_full_weight_le_three_endpoint_weight
    (r : ℝ)
    (hr : 0 ≤ r)
    (z : ℂ) :
    ‖z‖ ^ 2 * (1 + r + r ^ 2 + r ^ 3)
      ≤
    ‖z‖ ^ 2 * (3 * (1 + r ^ 3)) := by
  exact
    h3_radial_full_weight_mul_le_three_endpoint_weight_mul
      r
      (‖z‖ ^ 2)
      hr
      (sq_nonneg ‖z‖)

end

end Euclidean
end Bridge
end PrimeTensor
