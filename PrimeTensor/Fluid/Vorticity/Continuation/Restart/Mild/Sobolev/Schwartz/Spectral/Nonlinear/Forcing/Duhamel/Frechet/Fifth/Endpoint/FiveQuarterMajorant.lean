import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FiveQuarterHeat
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.SevenQuarterMajorant

/-!
# Fifth Fréchet endpoint: normalized five-quarter heat majorant

`FiveQuarterHeat` closes the residual heat multiplier needed after inserting
the selected forcing `11/4` Fourier moment into a full fourth Fourier moment.

This file normalizes its remaining lag coefficient.

Write

    C(ν,τ) = (sqrt(ν (τ/3)))⁻¹.

The exact second-moment identity gives

    C(ν,τ)^2 = 3 ν⁻¹ τ⁻¹.

The interpolated `5/4` heat coefficient is

    (C^1)^(3/4) (C^2)^(1/4)
      = C^(5/4)
      = (C^2)^(5/8).

Hence

    h3HeatFiveQuarterMomentCoefficient ν τ
      =
    (3 ν⁻¹)^(5/8) τ^(-5/8).

The terminal lag exponent `-5/8` is strictly greater than `-1`, so this
coefficient is integrable in source time all the way to the terminal endpoint.
Its exact primitive contributes the factor `(8/3) (t-a)^(3/8)`.

This is the scalar majorant required by the full-fourth Duhamel checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFiveQuarterMajorant
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Lag-independent coefficient in the normalized `5/4` heat majorant. -/
noncomputable def h3HeatFiveQuarterNormalizedCoefficient
    (ν : ℝ) : ℝ :=
  (3 * ν⁻¹) ^ ((5 : ℝ) / 8)

/-- Normalized terminal scalar majorant for the residual `5/4` heat weight. -/
noncomputable def h3HeatFiveQuarterTerminalMajorant
    (ν t s : ℝ) : ℝ :=
  h3HeatFiveQuarterNormalizedCoefficient ν *
    (t - s) ^ (-(5 : ℝ) / 8)

/-- The interpolated `5/4` heat coefficient is the `5/8` real power of the
exact second-moment coefficient. -/
theorem h3HeatFiveQuarterMomentCoefficient_eq_secondMomentCoefficient_rpow
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ) :
    h3HeatFiveQuarterMomentCoefficient ν τ
      =
    (3 * ν⁻¹ * τ⁻¹) ^ ((5 : ℝ) / 8) := by
  let C : ℝ :=
    (Real.sqrt (ν * (τ / 3)))⁻¹

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
      C ^ (2 : ℕ)
        =
      C ^ (2 : ℝ) :=
    (Real.rpow_natCast C 2).symm

  have h2Collapse :
      (C ^ (2 : ℝ)) ^ ((1 : ℝ) / 4)
        =
      C ^ ((2 : ℝ) * ((1 : ℝ) / 4)) :=
    (Real.rpow_mul
      hC.le
      (2 : ℝ)
      ((1 : ℝ) / 4)).symm

  have hCombine :
      C ^ ((3 : ℝ) / 4) *
          C ^ ((2 : ℝ) * ((1 : ℝ) / 4))
        =
      C ^
        (((3 : ℝ) / 4) +
          ((2 : ℝ) * ((1 : ℝ) / 4))) :=
    (Real.rpow_add
      hC
      ((3 : ℝ) / 4)
      ((2 : ℝ) * ((1 : ℝ) / 4))).symm

  have hScale :
      C ^ ((2 : ℝ) * ((5 : ℝ) / 8))
        =
      (C ^ (2 : ℝ)) ^ ((5 : ℝ) / 8) :=
    Real.rpow_mul
      hC.le
      (2 : ℝ)
      ((5 : ℝ) / 8)

  calc
    h3HeatFiveQuarterMomentCoefficient ν τ
        =
      (C ^ (1 : ℕ)) ^ ((3 : ℝ) / 4) *
        (C ^ (2 : ℕ)) ^ ((1 : ℝ) / 4) := by
      rfl
    _ =
      C ^ ((3 : ℝ) / 4) *
        (C ^ (2 : ℕ)) ^ ((1 : ℝ) / 4) := by
      rw [pow_one]
    _ =
      C ^ ((3 : ℝ) / 4) *
        (C ^ (2 : ℝ)) ^ ((1 : ℝ) / 4) := by
      rw [h2NatToReal]
    _ =
      C ^ ((3 : ℝ) / 4) *
        C ^ ((2 : ℝ) * ((1 : ℝ) / 4)) := by
      rw [h2Collapse]
    _ =
      C ^
        (((3 : ℝ) / 4) +
          ((2 : ℝ) * ((1 : ℝ) / 4))) :=
      hCombine
    _ =
      C ^ ((5 : ℝ) / 4) := by
      congr 1
      ring
    _ =
      C ^ ((2 : ℝ) * ((5 : ℝ) / 8)) := by
      congr 1
      ring
    _ =
      (C ^ (2 : ℝ)) ^ ((5 : ℝ) / 8) :=
      hScale
    _ =
      (C ^ (2 : ℕ)) ^ ((5 : ℝ) / 8) := by
      rw [← h2NatToReal]
    _ =
      (3 * ν⁻¹ * τ⁻¹) ^ ((5 : ℝ) / 8) := by
      rw [hC2]

/-- A positive inverse lag raised to `5/8` is exactly the `-5/8` power of the
lag. -/
theorem inv_rpow_five_eighth_eq_neg_five_eighth_rpow
    {q : ℝ}
    (hq : 0 < q) :
    (q⁻¹) ^ ((5 : ℝ) / 8)
      =
    q ^ (-(5 : ℝ) / 8) := by
  calc
    (q⁻¹) ^ ((5 : ℝ) / 8)
        =
      (q ^ (-(1 : ℝ))) ^ ((5 : ℝ) / 8) := by
      rw [Real.rpow_neg_one]
    _ =
      q ^ ((-(1 : ℝ)) * ((5 : ℝ) / 8)) := by
      exact
        (Real.rpow_mul
          hq.le
          (-(1 : ℝ))
          ((5 : ℝ) / 8)).symm
    _ =
      q ^ (-(5 : ℝ) / 8) := by
      congr 1
      ring

/-- Exact normalization of the `5/4` heat coefficient into a viscosity
coefficient times the universal terminal lag kernel `q^(-5/8)`. -/
theorem h3HeatFiveQuarterMomentCoefficient_eq_normalized
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ) :
    h3HeatFiveQuarterMomentCoefficient ν τ
      =
    h3HeatFiveQuarterNormalizedCoefficient ν *
      τ ^ (-(5 : ℝ) / 8) := by
  have hCoeff :=
    h3HeatFiveQuarterMomentCoefficient_eq_secondMomentCoefficient_rpow
      hν hτ

  have hBase0 :
      0 ≤ 3 * ν⁻¹ := by
    positivity

  have hInv0 :
      0 ≤ τ⁻¹ := by
    positivity

  have hSplit :
      (3 * ν⁻¹ * τ⁻¹) ^ ((5 : ℝ) / 8)
        =
      (3 * ν⁻¹) ^ ((5 : ℝ) / 8) *
        (τ⁻¹) ^ ((5 : ℝ) / 8) := by
    exact
      Real.mul_rpow hBase0 hInv0

  have hInv :
      (τ⁻¹) ^ ((5 : ℝ) / 8)
        =
      τ ^ (-(5 : ℝ) / 8) :=
    inv_rpow_five_eighth_eq_neg_five_eighth_rpow
      hτ

  unfold h3HeatFiveQuarterNormalizedCoefficient

  calc
    h3HeatFiveQuarterMomentCoefficient ν τ
        =
      (3 * ν⁻¹ * τ⁻¹) ^ ((5 : ℝ) / 8) :=
      hCoeff
    _ =
      (3 * ν⁻¹) ^ ((5 : ℝ) / 8) *
        (τ⁻¹) ^ ((5 : ℝ) / 8) :=
      hSplit
    _ =
      (3 * ν⁻¹) ^ ((5 : ℝ) / 8) *
        τ ^ (-(5 : ℝ) / 8) := by
      rw [hInv]

/-- Terminal-lag form of the normalized coefficient. -/
theorem h3HeatFiveQuarterMomentCoefficient_sub_eq_terminalMajorant
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t) :
    h3HeatFiveQuarterMomentCoefficient ν (t - s)
      =
    h3HeatFiveQuarterTerminalMajorant ν t s := by
  have hτ :
      0 < t - s :=
    sub_pos.mpr hs

  unfold h3HeatFiveQuarterTerminalMajorant

  exact
    h3HeatFiveQuarterMomentCoefficient_eq_normalized
      hν hτ

/-- The normalized `-5/8` terminal heat majorant is interval-integrable on
every finite interval. -/
theorem h3HeatFiveQuarterTerminalMajorant_intervalIntegrable
    {ν a t : ℝ} :
    IntervalIntegrable
      (h3HeatFiveQuarterTerminalMajorant ν t)
      volume
      a
      t := by
  have hPow :
      IntervalIntegrable
        (fun q : ℝ =>
          q ^ (-(5 : ℝ) / 8))
        volume
        0
        (t - a) := by
    exact
      intervalIntegral.intervalIntegrable_rpow'
        (by norm_num)

  have hShift :
      IntervalIntegrable
        (fun s : ℝ =>
          (t - s) ^ (-(5 : ℝ) / 8))
        volume
        a
        t := by
    have hComp :=
      hPow.comp_sub_left t
    simpa only [sub_zero, sub_sub_cancel] using hComp.symm

  unfold h3HeatFiveQuarterTerminalMajorant

  exact
    hShift.const_mul
      (h3HeatFiveQuarterNormalizedCoefficient ν)

/-- Exact time integral of the normalized `-5/8` terminal heat majorant. -/
theorem h3HeatFiveQuarterTerminalMajorant_integral_on
    {ν a t : ℝ}
    (_hat : a ≤ t) :
    (∫ s in a..t,
        h3HeatFiveQuarterTerminalMajorant ν t s)
      =
    ((8 : ℝ) / 3) *
      h3HeatFiveQuarterNormalizedCoefficient ν *
      (t - a) ^ ((3 : ℝ) / 8) := by
  have hReverse :
      (∫ s in a..t,
          (t - s) ^ (-(5 : ℝ) / 8))
        =
      ∫ q in (0 : ℝ)..(t - a),
          q ^ (-(5 : ℝ) / 8) := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (a := a)
        (b := t)
        (fun q : ℝ =>
          q ^ (-(5 : ℝ) / 8))
        t)

  have hPower :
      (∫ q in (0 : ℝ)..(t - a),
          q ^ (-(5 : ℝ) / 8))
        =
      ((8 : ℝ) / 3) *
        (t - a) ^ ((3 : ℝ) / 8) := by
    calc
      (∫ q in (0 : ℝ)..(t - a),
          q ^ (-(5 : ℝ) / 8))
          =
        ((t - a) ^ ((-(5 : ℝ) / 8) + 1) -
            (0 : ℝ) ^ ((-(5 : ℝ) / 8) + 1)) /
          (((-(5 : ℝ) / 8) + 1)) := by
            exact
              integral_rpow
                (a := (0 : ℝ))
                (b := t - a)
                (r := (-(5 : ℝ) / 8))
                (Or.inl (by norm_num))
      _ =
        ((8 : ℝ) / 3) *
          (t - a) ^ ((3 : ℝ) / 8) := by
        norm_num
        ring

  unfold h3HeatFiveQuarterTerminalMajorant

  calc
    (∫ s in a..t,
        h3HeatFiveQuarterNormalizedCoefficient ν *
          (t - s) ^ (-(5 : ℝ) / 8))
        =
      h3HeatFiveQuarterNormalizedCoefficient ν *
        (∫ s in a..t,
          (t - s) ^ (-(5 : ℝ) / 8)) := by
      rw [intervalIntegral.integral_const_mul]
    _ =
      h3HeatFiveQuarterNormalizedCoefficient ν *
        (∫ q in (0 : ℝ)..(t - a),
          q ^ (-(5 : ℝ) / 8)) := by
      rw [hReverse]
    _ =
      h3HeatFiveQuarterNormalizedCoefficient ν *
        (((8 : ℝ) / 3) *
          (t - a) ^ ((3 : ℝ) / 8)) := by
      rw [hPower]
    _ =
      ((8 : ℝ) / 3) *
        h3HeatFiveQuarterNormalizedCoefficient ν *
        (t - a) ^ ((3 : ℝ) / 8) := by
      ring

end
end Euclidean
end Bridge
end PrimeTensor
