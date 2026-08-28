import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.SevenQuarterHeat
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Third.Endpoint.NineQuarterMajorant

/-!
# Normalized seven-quarter heat majorant

`SevenQuarterHeat` closes the residual heat multiplier needed after inserting
the selected forcing `5/4` Fourier moment into a full third Fourier moment.

This file normalizes its remaining lag coefficient.

Write

    C(ν,τ) = (sqrt(ν (τ/3)))⁻¹.

The exact second-moment identity gives

    C(ν,τ)^2 = 3 ν⁻¹ τ⁻¹.

The interpolated `7/4` heat coefficient is

    (C^1)^(1/4) (C^2)^(3/4)
      = C^(7/4)
      = (C^2)^(7/8).

Hence

    h3HeatSevenQuarterMomentCoefficient ν τ
      =
    (3 ν⁻¹)^(7/8) τ^(-7/8).

The terminal lag exponent `-7/8` is strictly greater than `-1`, so this
coefficient is integrable in source time all the way to the terminal endpoint.

This is the scalar majorant required by the next full-third Duhamel checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSevenQuarterMajorant
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Lag-independent coefficient in the normalized `7/4` heat majorant. -/
noncomputable def h3HeatSevenQuarterNormalizedCoefficient
    (ν : ℝ) : ℝ :=
  (3 * ν⁻¹) ^ ((7 : ℝ) / 8)

/-- Normalized terminal scalar majorant for the residual `7/4` heat weight. -/
noncomputable def h3HeatSevenQuarterTerminalMajorant
    (ν t s : ℝ) : ℝ :=
  h3HeatSevenQuarterNormalizedCoefficient ν *
    (t - s) ^ (-(7 : ℝ) / 8)

/-- The interpolated `7/4` heat coefficient is the `7/8` real power of the
exact second-moment coefficient. -/
theorem h3HeatSevenQuarterMomentCoefficient_eq_secondMomentCoefficient_rpow
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ) :
    h3HeatSevenQuarterMomentCoefficient ν τ
      =
    (3 * ν⁻¹ * τ⁻¹) ^ ((7 : ℝ) / 8) := by
  let C : ℝ := (Real.sqrt (ν * (τ / 3)))⁻¹

  have hC : 0 < C := by
    dsimp only [C]
    positivity

  have hC2 :
      C ^ (2 : ℕ)
        =
      3 * ν⁻¹ * τ⁻¹ := by
    dsimp only [C]
    have h :=
      h3NonlinearForcingHeatSecondMomentCoefficient_sq_eq
        (ν := ν) (t := τ) (s := 0) hν hτ
    simpa only [sub_zero] using h

  have h2NatToReal :
      C ^ (2 : ℕ) = C ^ (2 : ℝ) :=
    (Real.rpow_natCast C 2).symm

  have h2Collapse :
      (C ^ (2 : ℝ)) ^ ((3 : ℝ) / 4)
        =
      C ^ ((2 : ℝ) * ((3 : ℝ) / 4)) :=
    (Real.rpow_mul hC.le (2 : ℝ) ((3 : ℝ) / 4)).symm

  have hCombine :
      C ^ ((1 : ℝ) / 4) *
          C ^ ((2 : ℝ) * ((3 : ℝ) / 4))
        =
      C ^
        (((1 : ℝ) / 4) +
          ((2 : ℝ) * ((3 : ℝ) / 4))) :=
    (Real.rpow_add hC
      ((1 : ℝ) / 4)
      ((2 : ℝ) * ((3 : ℝ) / 4))).symm

  have hScale :
      C ^ ((2 : ℝ) * ((7 : ℝ) / 8))
        =
      (C ^ (2 : ℝ)) ^ ((7 : ℝ) / 8) :=
    Real.rpow_mul hC.le (2 : ℝ) ((7 : ℝ) / 8)

  calc
    h3HeatSevenQuarterMomentCoefficient ν τ
        =
      (C ^ (1 : ℕ)) ^ ((1 : ℝ) / 4) *
        (C ^ (2 : ℕ)) ^ ((3 : ℝ) / 4) := by
      rfl
    _ =
      C ^ ((1 : ℝ) / 4) *
        (C ^ (2 : ℕ)) ^ ((3 : ℝ) / 4) := by
      rw [pow_one]
    _ =
      C ^ ((1 : ℝ) / 4) *
        (C ^ (2 : ℝ)) ^ ((3 : ℝ) / 4) := by
      rw [h2NatToReal]
    _ =
      C ^ ((1 : ℝ) / 4) *
        C ^ ((2 : ℝ) * ((3 : ℝ) / 4)) := by
      rw [h2Collapse]
    _ =
      C ^
        (((1 : ℝ) / 4) +
          ((2 : ℝ) * ((3 : ℝ) / 4))) :=
      hCombine
    _ =
      C ^ ((7 : ℝ) / 4) := by
      congr 1
      ring
    _ =
      C ^ ((2 : ℝ) * ((7 : ℝ) / 8)) := by
      congr 1
      ring
    _ =
      (C ^ (2 : ℝ)) ^ ((7 : ℝ) / 8) :=
      hScale
    _ =
      (C ^ (2 : ℕ)) ^ ((7 : ℝ) / 8) := by
      rw [← h2NatToReal]
    _ =
      (3 * ν⁻¹ * τ⁻¹) ^ ((7 : ℝ) / 8) := by
      rw [hC2]

/-- A positive inverse lag raised to `7/8` is exactly the `-7/8` power of the
lag. -/
theorem inv_rpow_seven_eighth_eq_neg_seven_eighth_rpow
    {q : ℝ}
    (hq : 0 < q) :
    (q⁻¹) ^ ((7 : ℝ) / 8)
      =
    q ^ (-(7 : ℝ) / 8) := by
  calc
    (q⁻¹) ^ ((7 : ℝ) / 8)
        =
      (q ^ (-(1 : ℝ))) ^ ((7 : ℝ) / 8) := by
      rw [Real.rpow_neg_one]
    _ =
      q ^ ((-(1 : ℝ)) * ((7 : ℝ) / 8)) := by
      exact
        (Real.rpow_mul
          hq.le
          (-(1 : ℝ))
          ((7 : ℝ) / 8)).symm
    _ =
      q ^ (-(7 : ℝ) / 8) := by
      congr 1
      ring

/-- Exact normalization of the `7/4` heat coefficient into a viscosity
coefficient times the universal terminal lag kernel `q^(-7/8)`. -/
theorem h3HeatSevenQuarterMomentCoefficient_eq_normalized
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ) :
    h3HeatSevenQuarterMomentCoefficient ν τ
      =
    h3HeatSevenQuarterNormalizedCoefficient ν *
      τ ^ (-(7 : ℝ) / 8) := by
  have hCoeff :=
    h3HeatSevenQuarterMomentCoefficient_eq_secondMomentCoefficient_rpow
      hν hτ

  have hBase0 : 0 ≤ 3 * ν⁻¹ := by
    positivity

  have hInv0 : 0 ≤ τ⁻¹ := by
    positivity

  have hSplit :
      (3 * ν⁻¹ * τ⁻¹) ^ ((7 : ℝ) / 8)
        =
      (3 * ν⁻¹) ^ ((7 : ℝ) / 8) *
        (τ⁻¹) ^ ((7 : ℝ) / 8) := by
    exact
      Real.mul_rpow hBase0 hInv0

  have hInv :
      (τ⁻¹) ^ ((7 : ℝ) / 8)
        =
      τ ^ (-(7 : ℝ) / 8) :=
    inv_rpow_seven_eighth_eq_neg_seven_eighth_rpow hτ

  unfold h3HeatSevenQuarterNormalizedCoefficient

  calc
    h3HeatSevenQuarterMomentCoefficient ν τ
        =
      (3 * ν⁻¹ * τ⁻¹) ^ ((7 : ℝ) / 8) :=
      hCoeff
    _ =
      (3 * ν⁻¹) ^ ((7 : ℝ) / 8) *
        (τ⁻¹) ^ ((7 : ℝ) / 8) :=
      hSplit
    _ =
      (3 * ν⁻¹) ^ ((7 : ℝ) / 8) *
        τ ^ (-(7 : ℝ) / 8) := by
      rw [hInv]

/-- Terminal-lag form of the normalized coefficient. -/
theorem h3HeatSevenQuarterMomentCoefficient_sub_eq_terminalMajorant
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t) :
    h3HeatSevenQuarterMomentCoefficient ν (t - s)
      =
    h3HeatSevenQuarterTerminalMajorant ν t s := by
  have hτ : 0 < t - s := sub_pos.mpr hs
  unfold h3HeatSevenQuarterTerminalMajorant
  exact
    h3HeatSevenQuarterMomentCoefficient_eq_normalized
      hν hτ

/-- The normalized `-7/8` terminal heat majorant is interval-integrable on
every finite interval. -/
theorem h3HeatSevenQuarterTerminalMajorant_intervalIntegrable
    {ν a t : ℝ} :
    IntervalIntegrable
      (h3HeatSevenQuarterTerminalMajorant ν t)
      volume
      a
      t := by
  have hPow :
      IntervalIntegrable
        (fun q : ℝ => q ^ (-(7 : ℝ) / 8))
        volume
        0
        (t - a) := by
    exact
      intervalIntegral.intervalIntegrable_rpow'
        (by norm_num)

  have hShift :
      IntervalIntegrable
        (fun s : ℝ =>
          (t - s) ^ (-(7 : ℝ) / 8))
        volume
        a
        t := by
    have hComp := hPow.comp_sub_left t
    simpa only [sub_zero, sub_sub_cancel] using hComp.symm

  unfold h3HeatSevenQuarterTerminalMajorant
  exact
    hShift.const_mul
      (h3HeatSevenQuarterNormalizedCoefficient ν)

/-- Exact time integral of the normalized `-7/8` terminal heat majorant. -/
theorem h3HeatSevenQuarterTerminalMajorant_integral_on
    {ν a t : ℝ}
    (_hat : a ≤ t) :
    (∫ s in a..t,
        h3HeatSevenQuarterTerminalMajorant ν t s)
      =
    8 *
      h3HeatSevenQuarterNormalizedCoefficient ν *
      (t - a) ^ ((1 : ℝ) / 8) := by
  have hReverse :
      (∫ s in a..t,
          (t - s) ^ (-(7 : ℝ) / 8))
        =
      ∫ q in (0 : ℝ)..(t - a),
          q ^ (-(7 : ℝ) / 8) := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (a := a)
        (b := t)
        (fun q : ℝ => q ^ (-(7 : ℝ) / 8))
        t)

  have hPower :
      (∫ q in (0 : ℝ)..(t - a),
          q ^ (-(7 : ℝ) / 8))
        =
      8 * (t - a) ^ ((1 : ℝ) / 8) := by
    calc
      (∫ q in (0 : ℝ)..(t - a),
          q ^ (-(7 : ℝ) / 8))
          =
        ((t - a) ^ ((-(7 : ℝ) / 8) + 1) -
            (0 : ℝ) ^ ((-(7 : ℝ) / 8) + 1)) /
          (((-(7 : ℝ) / 8) + 1)) := by
            exact
              integral_rpow
                (a := (0 : ℝ))
                (b := t - a)
                (r := (-(7 : ℝ) / 8))
                (Or.inl (by norm_num))
      _ =
        8 * (t - a) ^ ((1 : ℝ) / 8) := by
        norm_num
        ring

  unfold h3HeatSevenQuarterTerminalMajorant

  calc
    (∫ s in a..t,
        h3HeatSevenQuarterNormalizedCoefficient ν *
          (t - s) ^ (-(7 : ℝ) / 8))
        =
      h3HeatSevenQuarterNormalizedCoefficient ν *
        (∫ s in a..t,
          (t - s) ^ (-(7 : ℝ) / 8)) := by
      rw [intervalIntegral.integral_const_mul]
    _ =
      h3HeatSevenQuarterNormalizedCoefficient ν *
        (∫ q in (0 : ℝ)..(t - a),
          q ^ (-(7 : ℝ) / 8)) := by
      rw [hReverse]
    _ =
      h3HeatSevenQuarterNormalizedCoefficient ν *
        (8 * (t - a) ^ ((1 : ℝ) / 8)) := by
      rw [hPower]
    _ =
      8 *
        h3HeatSevenQuarterNormalizedCoefficient ν *
        (t - a) ^ ((1 : ℝ) / 8) := by
      ring

end
end Euclidean
end Bridge
end PrimeTensor
