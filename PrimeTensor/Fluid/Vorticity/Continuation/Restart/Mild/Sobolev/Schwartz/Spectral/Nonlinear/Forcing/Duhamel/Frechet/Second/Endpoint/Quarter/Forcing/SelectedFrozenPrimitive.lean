import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedSplit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Selected quarter-Hölder forcing: frozen terminal heat primitive

`Forcing.SelectedSplit` leaves exactly one terminal contribution outside the
head-plus-cancelled-tail budget: the forcing frozen at the terminal time.
Pointwise second heat moments have the apparent nonintegrable `q⁻¹` bound, so
that term should not be estimated one lag at a time.

Instead integrate the heat multiplier in lag first.  For fixed frequency,
with

    c = (2π)^2 ν,

we have

    ∫₀ᵀ |ξ|² exp (-c q |ξ|²) dq
      = c⁻¹ (1 - exp (-c T |ξ|²))
      ≤ c⁻¹.

Crucially, the antiderivative uses only `c⁻¹`; it never divides by `|ξ|²`, so
zero frequency requires no separate case.  This is the scalar heat primitive
needed to control the frozen terminal forcing by its existing Fourier `L¹`
mass.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedFrozenPrimitive
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact fixed-frequency time primitive for the second heat moment. -/
theorem h3HeatFourierSymbol_secondMoment_timeIntegral_eq
    {ν T : ℝ}
    (hν : 0 < ν)
    (hT : 0 ≤ T)
    (ξ : H3FourierPoint3) :
    (∫ q in (0 : ℝ)..T,
        ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖)
      =
    (((2 * Real.pi) ^ 2 * ν)⁻¹) *
      (1 - Real.exp
        (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) := by
  let c : ℝ := (2 * Real.pi) ^ 2 * ν
  let r2 : ℝ := ‖ξ‖ ^ 2

  have hc : 0 < c := by
    dsimp only [c]
    positivity

  have hc0 : c ≠ 0 := ne_of_gt hc

  have hnorm :
      ∀ q : ℝ,
        ‖h3HeatFourierSymbol ν q ξ‖
          = Real.exp (-(c * q * r2)) := by
    intro q
    unfold h3HeatFourierSymbol
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]

  let F : ℝ → ℝ :=
    fun q => -(c⁻¹) * Real.exp (-(c * q * r2))

  have hder :
      ∀ q : ℝ,
        HasDerivAt F
          (r2 * Real.exp (-(c * q * r2))) q := by
    intro q

    have hlin :
        HasDerivAt
          (fun x : ℝ => -(c * x * r2))
          (-(c * r2)) q := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id q).const_mul (-(c * r2)))

    have hexp :
        HasDerivAt
          (fun x : ℝ => Real.exp (-(c * x * r2)))
          (Real.exp (-(c * q * r2)) * -(c * r2)) q :=
      hlin.exp

    have hscaled :
        HasDerivAt F
          (-(c⁻¹) *
            (Real.exp (-(c * q * r2)) * -(c * r2))) q := by
      simpa [F] using hexp.const_mul (-(c⁻¹))

    have hcoef :
        (-(c⁻¹) *
            (Real.exp (-(c * q * r2)) * -(c * r2)))
          = r2 * Real.exp (-(c * q * r2)) := by
      field_simp [hc0]

    exact hscaled.congr_deriv hcoef

  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) T) := by
    apply Continuous.continuousOn
    dsimp only [F]
    fun_prop

  have hint :
      IntervalIntegrable
        (fun q : ℝ => r2 * Real.exp (-(c * q * r2)))
        volume
        0
        T := by
    apply ContinuousOn.intervalIntegrable
    fun_prop

  have hFTC :
      (∫ q in (0 : ℝ)..T,
          r2 * Real.exp (-(c * q * r2)))
        = F T - F 0 := by
    exact
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        hT hcont (fun q _hq => hder q) hint

  calc
    (∫ q in (0 : ℝ)..T,
        ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖)
        =
      ∫ q in (0 : ℝ)..T,
        r2 * Real.exp (-(c * q * r2)) := by
          apply intervalIntegral.integral_congr
          intro q _hq
          change
            ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖
              = r2 * Real.exp (-(c * q * r2))
          rw [hnorm q]
    _ = F T - F 0 := hFTC
    _ = c⁻¹ * (1 - Real.exp (-(c * T * r2))) := by
          dsimp only [F]
          simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero]
          ring
    _ =
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        (1 - Real.exp
          (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) := by
          simp only [c, r2]

/-- The fixed-frequency second heat moment has a uniform time-primitive bound
that depends only on viscosity, not on the terminal lag or frequency. -/
theorem h3HeatFourierSymbol_secondMoment_timeIntegral_le
    {ν T : ℝ}
    (hν : 0 < ν)
    (hT : 0 ≤ T)
    (ξ : H3FourierPoint3) :
    (∫ q in (0 : ℝ)..T,
        ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖)
      ≤
    ((2 * Real.pi) ^ 2 * ν)⁻¹ := by
  rw [h3HeatFourierSymbol_secondMoment_timeIntegral_eq hν hT ξ]

  have hc : 0 < (2 * Real.pi) ^ 2 * ν := by
    positivity

  have hcinv : 0 ≤ ((2 * Real.pi) ^ 2 * ν)⁻¹ :=
    inv_nonneg.mpr hc.le

  have hexp0 :
      0 ≤ Real.exp
        (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2)) :=
    (Real.exp_pos _).le

  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left
      (sub_le_self 1 hexp0)
      hcinv)

end

end Euclidean
end Bridge
end PrimeTensor
