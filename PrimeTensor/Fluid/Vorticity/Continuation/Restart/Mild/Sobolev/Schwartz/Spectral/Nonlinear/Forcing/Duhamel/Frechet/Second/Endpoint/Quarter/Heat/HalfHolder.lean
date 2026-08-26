import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.PositiveLag

/-!
# Positive-lag half-Hölder heat orbit in spectral H³

`Quarter.Heat.PositiveLag` proves the quantitative estimate

    ‖H_{a+h} U - H_a U‖
      ≤ sqrt ((2π)^2 ν h) * (sqrt (ν (a/3)))⁻¹ * ‖U‖.

For downstream time-regularity arguments it is more useful to expose the
increment dependence as an actual Hölder modulus.  Since `ν ≥ 0` and `h ≥ 0`,

    sqrt ((2π)^2 ν h)
      = sqrt ((2π)^2 ν) * sqrt h.

This file factors out the fixed positive-lag coefficient and records the scalar
and velocity estimates in the form

    ‖H_{a+h} U - H_a U‖ ≤ (L(ν,a) * ‖U‖) * sqrt h.

The coefficient depends only on the viscosity and the already elapsed positive
heat time.  The next step can therefore uniformize it on a terminal window
`a ≤ s < t` by using the lower bound on the base lag.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- Fixed coefficient in the positive-lag half-Hölder heat estimate. -/
noncomputable def h3HeatPositiveLagHalfHolderCoefficient
    (ν a : ℝ) : ℝ :=
  Real.sqrt ((2 * Real.pi) ^ 2 * ν) *
    (Real.sqrt (ν * (a / 3)))⁻¹

/-- The fixed positive-lag half-Hölder coefficient is nonnegative. -/
theorem h3HeatPositiveLagHalfHolderCoefficient_nonneg
    {ν a : ℝ}
    (hν : 0 ≤ ν)
    (ha : 0 ≤ a) :
    0 ≤ h3HeatPositiveLagHalfHolderCoefficient ν a := by
  unfold h3HeatPositiveLagHalfHolderCoefficient
  positivity

/-- One weighted spectral H³ scalar heat orbit is `1/2`-Hölder after a
strictly positive base heat time, with all increment dependence factored into
`sqrt h`. -/
theorem norm_h3SpectralScalarHeatApplyNN_add_sub_le_halfHolder_positiveLag
    {ν a h : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hh : 0 ≤ h)
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk (a + h) (add_nonneg ha.le hh)) G -
        h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk a ha.le) G‖
      ≤
    (h3HeatPositiveLagHalfHolderCoefficient ν a * ‖G‖) *
      Real.sqrt h := by
  have hBase :
      0 ≤ (2 * Real.pi) ^ 2 * ν := by
    positivity

  have hSqrt :
      Real.sqrt ((2 * Real.pi) ^ 2 * ν * h)
        =
      Real.sqrt ((2 * Real.pi) ^ 2 * ν) * Real.sqrt h := by
    rw [show
      (2 * Real.pi) ^ 2 * ν * h =
        ((2 * Real.pi) ^ 2 * ν) * h by
          ring]
    rw [Real.sqrt_mul hBase]

  calc
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk (a + h) (add_nonneg ha.le hh)) G -
        h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk a ha.le) G‖
        ≤
      (Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
        (Real.sqrt (ν * (a / 3)))⁻¹) * ‖G‖ :=
      norm_h3SpectralScalarHeatApplyNN_add_sub_le_positiveLag
        hν ha hh G
    _ =
      (h3HeatPositiveLagHalfHolderCoefficient ν a * ‖G‖) *
        Real.sqrt h := by
      unfold h3HeatPositiveLagHalfHolderCoefficient
      rw [hSqrt]
      ring

/-- The three-component weighted spectral H³ heat orbit has the same fixed
positive-lag `1/2`-Hölder modulus. -/
theorem norm_h3SpectralVelocityHeatApplyNN_add_sub_le_halfHolder_positiveLag
    {ν a h : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hh : 0 ≤ h)
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk (a + h) (add_nonneg ha.le hh)) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk a ha.le) U‖
      ≤
    (h3HeatPositiveLagHalfHolderCoefficient ν a * ‖U‖) *
      Real.sqrt h := by
  have hBase :
      0 ≤ (2 * Real.pi) ^ 2 * ν := by
    positivity

  have hSqrt :
      Real.sqrt ((2 * Real.pi) ^ 2 * ν * h)
        =
      Real.sqrt ((2 * Real.pi) ^ 2 * ν) * Real.sqrt h := by
    rw [show
      (2 * Real.pi) ^ 2 * ν * h =
        ((2 * Real.pi) ^ 2 * ν) * h by
          ring]
    rw [Real.sqrt_mul hBase]

  calc
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk (a + h) (add_nonneg ha.le hh)) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk a ha.le) U‖
        ≤
      (Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
        (Real.sqrt (ν * (a / 3)))⁻¹) * ‖U‖ :=
      norm_h3SpectralVelocityHeatApplyNN_add_sub_le_positiveLag
        hν ha hh U
    _ =
      (h3HeatPositiveLagHalfHolderCoefficient ν a * ‖U‖) *
        Real.sqrt h := by
      unfold h3HeatPositiveLagHalfHolderCoefficient
      rw [hSqrt]
      ring

end

end Euclidean
end Bridge
end PrimeTensor
