import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.Kernel.Selected
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Integrable quarter-power majorant for the old Duhamel history

For a positive retarded lag `τ`, the selected-restart kernel estimate from
`Quarter.Duhamel.Kernel.Selected` contains two pieces of heat smoothing:

* a quarter-increment factor at base time `τ/2`, contributing `τ^(-1/4)`;
* the ordinary heat--Leray kernel bound at time `τ/2`, contributing
  `τ^(-1/2)`.

Their product is therefore the integrable endpoint singularity `τ^(-3/4)`.
This file normalizes that scalar factor and records its exact time integral.
The next rung can then integrate the selected pointwise kernel estimate over
the old Volterra history without reopening the real-power algebra.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval NNReal

noncomputable section

/-- A square root of a reciprocal square root is the negative quarter power
on nonnegative inputs. -/
theorem Real.sqrt_inv_sqrt_eq_rpow_neg_quarter
    {x : ℝ}
    (hx : 0 ≤ x) :
    Real.sqrt ((Real.sqrt x)⁻¹)
      = x ^ (-(1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow]
  rw [h3_inv_sqrt_eq_rpow_neg_half hx]
  calc
    (x ^ (-(1 / 2 : ℝ))) ^ ((1 : ℝ) / 2)
        = x ^ ((-(1 / 2 : ℝ)) * ((1 : ℝ) / 2)) := by
          rw [← Real.rpow_mul hx]
    _ = x ^ (-(1 : ℝ) / 4) := by
          congr 1
          ring

/-- Time-independent coefficient left after extracting the increment
`h^(1/4)` and retarded singularity `τ^(-3/4)` from the history-kernel
majorant. -/
noncomputable def h3DuhamelQuarterHistoryPowerCoefficient
    (ν MU MV : ℝ) : ℝ :=
  (((2 * Real.pi) ^ 2 * ν) ^ ((1 : ℝ) / 4)) *
    ((ν / 6) ^ (-(1 : ℝ) / 4)) *
    (288 * h3SobolevDeweightingConstant *
      ((ν / 2) ^ (-(1 : ℝ) / 2)) * MU * MV)

/-- The normalized history coefficient is nonnegative for nonnegative
viscosity and state bounds. -/
theorem h3DuhamelQuarterHistoryPowerCoefficient_nonneg
    {ν MU MV : ℝ}
    (hν : 0 ≤ ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV) :
    0 ≤ h3DuhamelQuarterHistoryPowerCoefficient ν MU MV := by
  unfold h3DuhamelQuarterHistoryPowerCoefficient
  positivity [h3SobolevDeweightingConstant_nonneg]

/-- Exact normalization of the positive-lag quarter-history kernel. -/
theorem h3DuhamelQuarterHistoryKernelMajorant_eq_power
    {ν τ h MU MV : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (hh : 0 ≤ h) :
    h3DuhamelQuarterHistoryKernelMajorant ν τ h MU MV
      =
    h3DuhamelQuarterHistoryPowerCoefficient ν MU MV *
      h ^ ((1 : ℝ) / 4) *
      τ ^ (-(3 : ℝ) / 4) := by
  have hν6 : 0 ≤ ν / 6 := by positivity
  have hν2 : 0 ≤ ν / 2 := by positivity
  have hbase : 0 ≤ (2 * Real.pi) ^ 2 * ν := by positivity
  have hτ0 : 0 ≤ τ := hτ.le

  have hInc :
      (((2 * Real.pi) ^ 2 * ν * h) ^ ((1 : ℝ) / 4))
        =
      (((2 * Real.pi) ^ 2 * ν) ^ ((1 : ℝ) / 4)) *
        h ^ ((1 : ℝ) / 4) := by
    rw [show (2 * Real.pi) ^ 2 * ν * h =
        ((2 * Real.pi) ^ 2 * ν) * h by ring]
    rw [Real.mul_rpow hbase hh]

  have hQuarter :
      Real.sqrt ((Real.sqrt (ν * ((τ / 2) / 3)))⁻¹)
        =
      (ν / 6) ^ (-(1 : ℝ) / 4) *
        τ ^ (-(1 : ℝ) / 4) := by
    rw [show ν * ((τ / 2) / 3) = (ν / 6) * τ by ring]
    rw [Real.sqrt_inv_sqrt_eq_rpow_neg_quarter
      (mul_nonneg hν6 hτ0)]
    rw [Real.mul_rpow hν6 hτ0]

  have hHalf :
      (Real.sqrt (ν * (τ / 2)))⁻¹
        =
      (ν / 2) ^ (-(1 : ℝ) / 2) *
        τ ^ (-(1 : ℝ) / 2) := by
    rw [show ν * (τ / 2) = (ν / 2) * τ by ring]
    rw [h3_inv_sqrt_eq_rpow_neg_half (mul_nonneg hν2 hτ0)]
    rw [Real.mul_rpow hν2 hτ0]
    simp only [neg_div]

  have hTau :
      τ ^ (-(1 : ℝ) / 4) *
          τ ^ (-(1 : ℝ) / 2)
        =
      τ ^ (-(3 : ℝ) / 4) := by
    calc
      τ ^ (-(1 : ℝ) / 4) *
          τ ^ (-(1 : ℝ) / 2)
          =
        τ ^ (-(1 : ℝ) / 4 + (-(1 : ℝ) / 2)) := by
          rw [Real.rpow_add hτ]
      _ = τ ^ (-(3 : ℝ) / 4) := by
          congr 1
          ring

  unfold h3DuhamelQuarterHistoryKernelMajorant
  unfold h3HeatQuarterIncrementCoefficient
  unfold h3DuhamelQuarterHistoryPowerCoefficient
  rw [hInc, hQuarter, hHalf]
  rw [← hTau]
  ring

/-- Scalar old-history majorant at terminal time `t`, after the retarded lag
has been written as `t-s`. -/
noncomputable def h3DuhamelQuarterHistoryTimeMajorant
    (ν t h MU MV s : ℝ) : ℝ :=
  h3DuhamelQuarterHistoryPowerCoefficient ν MU MV *
    h ^ ((1 : ℝ) / 4) *
    (t - s) ^ (-(3 : ℝ) / 4)

/-- The old-history scalar singularity is interval-integrable. -/
theorem h3DuhamelQuarterHistoryTimeMajorant_intervalIntegrable
    {ν t h MU MV : ℝ} :
    IntervalIntegrable
      (h3DuhamelQuarterHistoryTimeMajorant ν t h MU MV)
      volume
      0
      t := by
  have hPow :
      IntervalIntegrable
        (fun q : ℝ => q ^ (-(3 : ℝ) / 4))
        volume
        0
        t := by
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)

  have hShift :
      IntervalIntegrable
        (fun s : ℝ => (t - s) ^ (-(3 : ℝ) / 4))
        volume
        0
        t := by
    have hComp := hPow.comp_sub_left t
    simpa only [sub_zero, sub_self, sub_sub_cancel] using hComp.symm

  unfold h3DuhamelQuarterHistoryTimeMajorant
  exact
    hShift.const_mul
      (h3DuhamelQuarterHistoryPowerCoefficient ν MU MV *
        h ^ ((1 : ℝ) / 4))

/-- Exact integral of the normalized old-history singularity. -/
theorem h3DuhamelQuarterHistoryTimeMajorant_integral
    {ν t h MU MV : ℝ}
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        h3DuhamelQuarterHistoryTimeMajorant ν t h MU MV s)
      =
    4 * h3DuhamelQuarterHistoryPowerCoefficient ν MU MV *
      h ^ ((1 : ℝ) / 4) *
      t ^ ((1 : ℝ) / 4) := by
  let C : ℝ :=
    h3DuhamelQuarterHistoryPowerCoefficient ν MU MV *
      h ^ ((1 : ℝ) / 4)

  have hReverse :
      (∫ s in (0 : ℝ)..t,
          (t - s) ^ (-(3 : ℝ) / 4))
        =
      ∫ q in (0 : ℝ)..t,
          q ^ (-(3 : ℝ) / 4) := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (a := (0 : ℝ))
        (b := t)
        (fun q : ℝ => q ^ (-(3 : ℝ) / 4))
        t)

  have hPower :
      (∫ q in (0 : ℝ)..t,
          q ^ (-(3 : ℝ) / 4))
        =
      4 * t ^ ((1 : ℝ) / 4) := by
    calc
      (∫ q in (0 : ℝ)..t,
          q ^ (-(3 : ℝ) / 4))
          =
        (t ^ ((-(3 : ℝ) / 4) + 1) -
            (0 : ℝ) ^ ((-(3 : ℝ) / 4) + 1)) /
          (((-(3 : ℝ) / 4) + 1)) := by
            exact
              integral_rpow
                (a := (0 : ℝ))
                (b := t)
                (r := (-(3 : ℝ) / 4))
                (Or.inl (by norm_num))
      _ = 4 * t ^ ((1 : ℝ) / 4) := by
            rw [show (-(3 : ℝ) / 4) + 1 = (1 : ℝ) / 4 by ring]
            rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 4 ≠ 0)]
            ring

  unfold h3DuhamelQuarterHistoryTimeMajorant
  rw [intervalIntegral.integral_const_mul]
  rw [hReverse, hPower]
  ring

/-- On a strict history slice the selected positive-lag kernel majorant is
exactly the normalized `-3/4` time majorant. -/
theorem h3DuhamelQuarterHistoryKernelMajorant_eq_timeMajorant
    {ν t h MU MV s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (hh : 0 ≤ h) :
    h3DuhamelQuarterHistoryKernelMajorant
        ν (t - s) h MU MV
      =
    h3DuhamelQuarterHistoryTimeMajorant
        ν t h MU MV s := by
  rw [h3DuhamelQuarterHistoryKernelMajorant_eq_power
    hν (sub_pos.mpr hs) hh]
  rfl

end

end Euclidean
end Bridge
end PrimeTensor
