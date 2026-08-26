import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.State
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Heat.Semigroup

/-!
# Uniform quarter-Hölder heat increments after a positive base time

The state estimate in `Quarter.Heat.State` controls one increment

    ‖H_{a+h} U - H_a U‖
      ≤ Q(ν,a,h) ‖U‖

at a positive base heat time `a`.

For the endpoint argument we need the same estimate uniformly after any
additional elapsed heat time `b`.  The semigroup law gives

    H_{a+b+h} U - H_{a+b} U
      = H_b (H_{a+h} U - H_a U),

and heat contraction therefore removes `b` completely.  We then factor the
explicit coefficient as

    Q(ν,a,h) = L_heat(ν,a) h^(1/4).

This is the reusable positive-base heat-orbit modulus needed when the selected
mild path is split into its free heat part and nonlinear Duhamel part.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open scoped NNReal

noncomputable section

/-- The time-independent coefficient in the positive-base quarter-Hölder heat
orbit estimate. -/
noncomputable def h3HeatQuarterOrbitCoefficient
    (ν a : ℝ) : ℝ :=
  (((2 * Real.pi) ^ 2 * ν) ^ ((1 : ℝ) / 4)) *
    Real.sqrt ((Real.sqrt (ν * (a / 3)))⁻¹)

/-- The positive-base heat-orbit coefficient is nonnegative for nonnegative
viscosity. -/
theorem h3HeatQuarterOrbitCoefficient_nonneg
    {ν a : ℝ}
    (hν : 0 ≤ ν) :
    0 ≤ h3HeatQuarterOrbitCoefficient ν a := by
  unfold h3HeatQuarterOrbitCoefficient
  have hbase : 0 ≤ (2 * Real.pi) ^ 2 * ν := by
    exact mul_nonneg (sq_nonneg _) hν
  exact
    mul_nonneg
      (Real.rpow_nonneg hbase _)
      (Real.sqrt_nonneg _)

/-- The increment coefficient from `Quarter.Heat.State` factors into a fixed
positive-base coefficient times the quarter power of the increment. -/
theorem h3HeatQuarterIncrementCoefficient_eq_orbit_mul_rpow
    {ν a h : ℝ}
    (hν : 0 ≤ ν)
    (hh : 0 ≤ h) :
    h3HeatQuarterIncrementCoefficient ν a h
      =
    h3HeatQuarterOrbitCoefficient ν a *
      h ^ ((1 : ℝ) / 4) := by
  unfold h3HeatQuarterIncrementCoefficient
  unfold h3HeatQuarterOrbitCoefficient
  have hbase : 0 ≤ (2 * Real.pi) ^ 2 * ν := by
    exact mul_nonneg (sq_nonneg _) hν
  rw [show (2 * Real.pi) ^ 2 * ν * h =
      ((2 * Real.pi) ^ 2 * ν) * h by ring]
  rw [Real.mul_rpow hbase hh]
  ring

/-- Adding any further elapsed heat time after the positive base cannot enlarge
an increment.  This is the semigroup form of the state-level quarter estimate. -/
theorem norm_h3SpectralVelocityHeatApplyNN_add_add_sub_le_quarter
    {ν : ℝ}
    (hν : 0 < ν)
    (a b h : ℝ≥0)
    (ha : 0 < (a : ℝ))
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (a + b + h) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (a + b) U‖
      ≤
    h3HeatQuarterIncrementCoefficient
        ν (a : ℝ) (h : ℝ) *
      ‖U‖ := by
  have htime : a + b + h = (a + h) + b := by
    ac_rfl

  rw [htime]
  rw [
    h3SpectralVelocityHeatApplyNN_add_time
      ν hν.le (a + h) b U,
    h3SpectralVelocityHeatApplyNN_add_time
      ν hν.le a b U
  ]

  calc
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le b
          (h3SpectralVelocityHeatApplyNN ν hν.le (a + h) U) -
        h3SpectralVelocityHeatApplyNN
          ν hν.le b
          (h3SpectralVelocityHeatApplyNN ν hν.le a U)‖
        =
      ‖h3SpectralVelocityHeatCLM ν hν.le b
          (h3SpectralVelocityHeatApplyNN ν hν.le (a + h) U -
            h3SpectralVelocityHeatApplyNN ν hν.le a U)‖ := by
      simp only [map_sub, h3SpectralVelocityHeatCLM_apply]
    _ ≤
      ‖h3SpectralVelocityHeatApplyNN ν hν.le (a + h) U -
        h3SpectralVelocityHeatApplyNN ν hν.le a U‖ := by
      exact
        norm_h3SpectralVelocityHeatCLM_apply_le
          ν hν.le b
          (h3SpectralVelocityHeatApplyNN ν hν.le (a + h) U -
            h3SpectralVelocityHeatApplyNN ν hν.le a U)
    _ ≤
      h3HeatQuarterIncrementCoefficient
          ν (a : ℝ) (h : ℝ) *
        ‖U‖ := by
      exact
        norm_h3SpectralVelocityHeatApplyNN_add_sub_le_quarter
          hν a h ha U

/-- Uniform quarter-Hölder form of the previous theorem.  The coefficient is
independent of the additional elapsed time `b`. -/
theorem norm_h3SpectralVelocityHeatApplyNN_add_add_sub_le_quarter_rpow
    {ν : ℝ}
    (hν : 0 < ν)
    (a b h : ℝ≥0)
    (ha : 0 < (a : ℝ))
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (a + b + h) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (a + b) U‖
      ≤
    (h3HeatQuarterOrbitCoefficient ν (a : ℝ) * ‖U‖) *
      (h : ℝ) ^ ((1 : ℝ) / 4) := by
  calc
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (a + b + h) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (a + b) U‖
        ≤
      h3HeatQuarterIncrementCoefficient
          ν (a : ℝ) (h : ℝ) *
        ‖U‖ :=
      norm_h3SpectralVelocityHeatApplyNN_add_add_sub_le_quarter
        hν a b h ha U
    _ =
      (h3HeatQuarterOrbitCoefficient ν (a : ℝ) * ‖U‖) *
        (h : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [
        h3HeatQuarterIncrementCoefficient_eq_orbit_mul_rpow
          (ν := ν) (a := (a : ℝ)) (h := (h : ℝ))
          hν.le h.property
      ]
      ring

end

end Euclidean
end Bridge
end PrimeTensor
