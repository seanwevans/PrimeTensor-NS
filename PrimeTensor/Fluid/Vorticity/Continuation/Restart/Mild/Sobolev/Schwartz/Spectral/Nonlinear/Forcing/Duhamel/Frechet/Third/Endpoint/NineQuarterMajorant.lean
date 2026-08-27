import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Third.Endpoint.NineQuarterVariation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter

/-!
# Nine-quarter endpoint scalar majorant

The Fourier-space `9/4` endpoint variation estimate is already closed.  This
file normalizes its remaining scalar lag coefficient.

Write

    C(ν,τ) = (sqrt(ν (τ/3)))⁻¹.

The existing second-moment identity gives exactly

    C(ν,τ)^2 = 3 ν⁻¹ τ⁻¹.

The interpolated `9/4` heat coefficient is

    (C^2)^(3/4) (C^3)^(1/4)
      = C^(9/4)
      = (C^2)^(9/8).

Substituting the exact square identity and multiplying by the selected
quarter-Hölder factor `τ^(1/4)` gives

    ((3 ν⁻¹)^(9/8) K) τ^(-7/8).

The exponent `-7/8` is strictly greater than `-1`, hence the terminal
source-time kernel is interval-integrable.  Its exact integral contributes the
finite factor

    8 (t-a)^(1/8).

This is the scalar endpoint budget needed for the first fractional bootstrap
past two Fourier moments.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdEndpointNineQuarterMajorant
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Lag-independent coefficient of the normalized `-7/8` cancellation
majorant. -/
noncomputable def h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
    (ν K : ℝ) : ℝ :=
  (3 * ν⁻¹) ^ ((9 : ℝ) / 8) * K

/-- Normalized scalar majorant for the `9/4` endpoint variation term. -/
noncomputable def h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
    (ν t K s : ℝ) : ℝ :=
  h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient ν K *
    (t - s) ^ (-(7 : ℝ) / 8)

/-- The interpolated `9/4` heat coefficient is the `9/8` real power of the
exact second-moment coefficient. -/
theorem h3HeatNineQuarterMomentCoefficient_eq_secondMomentCoefficient_rpow
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ) :
    h3HeatNineQuarterMomentCoefficient ν τ
      =
    (3 * ν⁻¹ * τ⁻¹) ^ ((9 : ℝ) / 8) := by
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

  have h3NatToReal :
      C ^ (3 : ℕ) = C ^ (3 : ℝ) :=
    (Real.rpow_natCast C 3).symm

  have h2Collapse :
      (C ^ (2 : ℝ)) ^ ((3 : ℝ) / 4)
        =
      C ^ ((2 : ℝ) * ((3 : ℝ) / 4)) :=
    (Real.rpow_mul hC.le (2 : ℝ) ((3 : ℝ) / 4)).symm

  have h3Collapse :
      (C ^ (3 : ℝ)) ^ ((1 : ℝ) / 4)
        =
      C ^ ((3 : ℝ) * ((1 : ℝ) / 4)) :=
    (Real.rpow_mul hC.le (3 : ℝ) ((1 : ℝ) / 4)).symm

  have hCombine :
      C ^ ((2 : ℝ) * ((3 : ℝ) / 4)) *
          C ^ ((3 : ℝ) * ((1 : ℝ) / 4))
        =
      C ^
        (((2 : ℝ) * ((3 : ℝ) / 4)) +
          ((3 : ℝ) * ((1 : ℝ) / 4))) :=
    (Real.rpow_add hC
      ((2 : ℝ) * ((3 : ℝ) / 4))
      ((3 : ℝ) * ((1 : ℝ) / 4))).symm

  have hScale :
      C ^ ((2 : ℝ) * ((9 : ℝ) / 8))
        =
      (C ^ (2 : ℝ)) ^ ((9 : ℝ) / 8) :=
    Real.rpow_mul hC.le (2 : ℝ) ((9 : ℝ) / 8)

  calc
    h3HeatNineQuarterMomentCoefficient ν τ
        =
      (C ^ (2 : ℕ)) ^ ((3 : ℝ) / 4) *
        (C ^ (3 : ℕ)) ^ ((1 : ℝ) / 4) := by
      rfl
    _ =
      (C ^ (2 : ℝ)) ^ ((3 : ℝ) / 4) *
        (C ^ (3 : ℝ)) ^ ((1 : ℝ) / 4) := by
      rw [h2NatToReal, h3NatToReal]
    _ =
      C ^ ((2 : ℝ) * ((3 : ℝ) / 4)) *
        C ^ ((3 : ℝ) * ((1 : ℝ) / 4)) := by
      rw [h2Collapse, h3Collapse]
    _ =
      C ^
        (((2 : ℝ) * ((3 : ℝ) / 4)) +
          ((3 : ℝ) * ((1 : ℝ) / 4))) :=
      hCombine
    _ =
      C ^ ((9 : ℝ) / 4) := by
      congr 1
      ring
    _ =
      C ^ ((2 : ℝ) * ((9 : ℝ) / 8)) := by
      congr 1
      ring
    _ =
      (C ^ (2 : ℝ)) ^ ((9 : ℝ) / 8) :=
      hScale
    _ =
      (C ^ (2 : ℕ)) ^ ((9 : ℝ) / 8) := by
      rw [← h2NatToReal]
    _ =
      (3 * ν⁻¹ * τ⁻¹) ^ ((9 : ℝ) / 8) := by
      rw [hC2]

/-- A positive inverse lag raised to `9/8` is exactly the `-9/8` power of the
lag. -/
theorem inv_rpow_nine_eighth_eq_neg_nine_eighth_rpow
    {q : ℝ}
    (hq : 0 < q) :
    (q⁻¹) ^ ((9 : ℝ) / 8)
      =
    q ^ (-(9 : ℝ) / 8) := by
  calc
    (q⁻¹) ^ ((9 : ℝ) / 8)
        =
      (q ^ (-(1 : ℝ))) ^ ((9 : ℝ) / 8) := by
      rw [Real.rpow_neg_one]
    _ =
      q ^ ((-(1 : ℝ)) * ((9 : ℝ) / 8)) := by
      exact
        (Real.rpow_mul
          hq.le
          (-(1 : ℝ))
          ((9 : ℝ) / 8)).symm
    _ =
      q ^ (-(9 : ℝ) / 8) := by
      congr 1
      ring

/-- The `-9/8` heat lag paired with a quarter power is exactly the integrable
`-7/8` terminal singularity. -/
theorem neg_nine_eighth_rpow_mul_quarter_eq_neg_seven_eighth_rpow
    {q : ℝ}
    (hq : 0 < q) :
    q ^ (-(9 : ℝ) / 8) *
        q ^ ((1 : ℝ) / 4)
      =
    q ^ (-(7 : ℝ) / 8) := by
  calc
    q ^ (-(9 : ℝ) / 8) *
        q ^ ((1 : ℝ) / 4)
        =
      q ^
        ((-(9 : ℝ) / 8) + ((1 : ℝ) / 4)) := by
      rw [← Real.rpow_add hq]
    _ =
      q ^ (-(7 : ℝ) / 8) := by
      congr 1
      ring

/-- Exact normalization of the `9/4` quarter-Hölder cancellation profile to
the universal `-7/8` scalar kernel. -/
theorem h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile_eq_majorant
    {ν t K s : ℝ}
    (hν : 0 < ν)
    (hs : s < t) :
    h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile
        ν t K s
      =
    h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
        ν t K s := by
  let q : ℝ := t - s
  have hq : 0 < q := by
    dsimp only [q]
    exact sub_pos.mpr hs

  have hCoeff :
      h3HeatNineQuarterMomentCoefficient ν q
        =
      (3 * ν⁻¹ * q⁻¹) ^ ((9 : ℝ) / 8) :=
    h3HeatNineQuarterMomentCoefficient_eq_secondMomentCoefficient_rpow
      hν hq

  have hBase0 : 0 ≤ 3 * ν⁻¹ := by
    positivity

  have hInv0 : 0 ≤ q⁻¹ := by
    positivity

  have hSplit :
      (3 * ν⁻¹ * q⁻¹) ^ ((9 : ℝ) / 8)
        =
      (3 * ν⁻¹) ^ ((9 : ℝ) / 8) *
        (q⁻¹) ^ ((9 : ℝ) / 8) := by
    exact
      Real.mul_rpow hBase0 hInv0

  have hInv :
      (q⁻¹) ^ ((9 : ℝ) / 8)
        =
      q ^ (-(9 : ℝ) / 8) :=
    inv_rpow_nine_eighth_eq_neg_nine_eighth_rpow hq

  have hLag :
      q ^ (-(9 : ℝ) / 8) *
          q ^ ((1 : ℝ) / 4)
        =
      q ^ (-(7 : ℝ) / 8) :=
    neg_nine_eighth_rpow_mul_quarter_eq_neg_seven_eighth_rpow hq

  unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile
  unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
  unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient

  change
    h3HeatNineQuarterMomentCoefficient ν q *
        (K * q ^ ((1 : ℝ) / 4))
      =
    ((3 * ν⁻¹) ^ ((9 : ℝ) / 8) * K) *
      q ^ (-(7 : ℝ) / 8)

  calc
    h3HeatNineQuarterMomentCoefficient ν q *
        (K * q ^ ((1 : ℝ) / 4))
        =
      (3 * ν⁻¹ * q⁻¹) ^ ((9 : ℝ) / 8) *
        (K * q ^ ((1 : ℝ) / 4)) := by
      rw [hCoeff]
    _ =
      ((3 * ν⁻¹) ^ ((9 : ℝ) / 8) *
          (q⁻¹) ^ ((9 : ℝ) / 8)) *
        (K * q ^ ((1 : ℝ) / 4)) := by
      rw [hSplit]
    _ =
      ((3 * ν⁻¹) ^ ((9 : ℝ) / 8) *
          q ^ (-(9 : ℝ) / 8)) *
        (K * q ^ ((1 : ℝ) / 4)) := by
      rw [hInv]
    _ =
      ((3 * ν⁻¹) ^ ((9 : ℝ) / 8) * K) *
        (q ^ (-(9 : ℝ) / 8) *
          q ^ ((1 : ℝ) / 4)) := by
      ring
    _ =
      ((3 * ν⁻¹) ^ ((9 : ℝ) / 8) * K) *
        q ^ (-(7 : ℝ) / 8) := by
      rw [hLag]

/-- The normalized `-7/8` scalar majorant is interval-integrable on every
finite terminal interval. -/
theorem h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant_intervalIntegrable
    {ν a t K : ℝ} :
    IntervalIntegrable
      (h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
        ν t K)
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

  unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
  exact
    hShift.const_mul
      (h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
        ν K)

/-- Exact time integral of the normalized `-7/8` majorant. -/
theorem h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant_integral_on
    {ν a t K : ℝ}
    (_hat : a ≤ t) :
    (∫ s in a..t,
        h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
          ν t K s)
      =
    8 *
      h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
        ν K *
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
        rw [show (-(7 : ℝ) / 8) + 1 = (1 : ℝ) / 8 by ring]
        rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 8 ≠ 0)]
        ring

  unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
  rw [intervalIntegral.integral_const_mul]
  rw [hReverse, hPower]
  ring

/-- Generic `9/4` endpoint variation estimate in normalized `-7/8` form. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_nineQuarter_le_majorant
    {ν a t K s : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo a t)
    (hHolder :
      H3NonlinearForcingEndpointQuarterHolderL1On
        U V a t K i) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
              h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ)‖)
      ≤
    h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
      ν t K s := by
  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
              h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ)‖)
        ≤
      h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile
        ν t K s :=
      h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_nineQuarter_le_quarter
        hν U V i hs hHolder
    _ =
      h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
        ν t K s :=
      h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile_eq_majorant
        hν hs.2

/-- Selected-restart `9/4` endpoint variation estimate in normalized
`-7/8` form. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_nineQuarter_le_majorant_selectedRestart
    {ν A a t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : s ∈ Set.Ioo a t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖)
      ≤
    h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
      ν t
        (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A a t)
        s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hHolder :
      H3NonlinearForcingEndpointQuarterHolderL1On
        W W a t
        (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A a t)
        i := by
    dsimp only [W]
    exact
      h3NonlinearForcingEndpointQuarterHolderL1On_selectedRestart
        hν U₀ hA hU₀ ha hat htR i

  exact
    h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_nineQuarter_le_majorant
      hν W W i hs hHolder

/-- Selected normalized `-7/8` majorant is interval-integrable. -/
theorem h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant_intervalIntegrable_selectedRestart
    {ν A a t : ℝ} :
    IntervalIntegrable
      (h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
        ν t
        (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A a t))
      volume
      a
      t := by
  exact
    h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant_intervalIntegrable

end
end Euclidean
end Bridge
end PrimeTensor
