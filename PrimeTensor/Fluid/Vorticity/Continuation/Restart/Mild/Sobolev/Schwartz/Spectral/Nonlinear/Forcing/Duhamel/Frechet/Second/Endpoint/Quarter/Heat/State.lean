import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.Increment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Moment.Smoothing

/-!
# Quarter-Hölder heat increments in the weighted spectral H³ state

The scalar multiplier estimate from `Quarter.Heat.Increment` is now lifted to
the actual weighted spectral H³ solver state.

For a positive base heat time `a`, one full Fourier moment of `H_a` is already
uniformly controlled by `Heat.Moment.Smoothing`.  Interpolating that first
moment with the heat contraction gives the half Fourier moment needed by the
quarter-power time increment.

The resulting explicit coefficient is

    Q(ν,a,h)
      = (((2π)^2 ν h)^(1/4))
          * sqrt ((sqrt (ν (a/3)))⁻¹),

and

    ‖H_{a+h} G - H_a G‖ ≤ Q(ν,a,h) ‖G‖.

The final theorem lifts this componentwise to the three-component spectral H³
velocity state.  This is the semigroup estimate needed to control the
positive-time restart contribution of the mild path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralQuarterHeatState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit quarter-Hölder coefficient for a heat orbit with positive base
heat time `a`. -/
noncomputable def h3HeatQuarterIncrementCoefficient
    (ν a h : ℝ) : ℝ :=
  (((2 * Real.pi) ^ 2 * ν * h) ^ ((1 : ℝ) / 4)) *
    Real.sqrt ((Real.sqrt (ν * (a / 3)))⁻¹)

/-- The quarter-Hölder heat coefficient is nonnegative for nonnegative
viscosity, base time, and increment. -/
theorem h3HeatQuarterIncrementCoefficient_nonneg
    {ν a h : ℝ}
    (hν : 0 ≤ ν)
    (_ha : 0 ≤ a)
    (hh : 0 ≤ h) :
    0 ≤ h3HeatQuarterIncrementCoefficient ν a h := by
  unfold h3HeatQuarterIncrementCoefficient
  exact
    mul_nonneg
      (Real.rpow_nonneg (by positivity) _)
      (Real.sqrt_nonneg _)

/-- Uniform frequency bound obtained by interpolating the first positive-time
heat moment with heat contraction. -/
theorem norm_h3HeatFourierSymbol_add_sub_le_quarter_uniform
    {ν a h : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hh : 0 ≤ h)
    (ξ : H3FourierPoint3) :
    ‖h3HeatFourierSymbol ν (a + h) ξ -
        h3HeatFourierSymbol ν a ξ‖
      ≤
    h3HeatQuarterIncrementCoefficient ν a h := by
  let B : ℝ := (2 * Real.pi) ^ 2 * ν * h
  let C : ℝ := (Real.sqrt (ν * (a / 3)))⁻¹
  let r : ℝ := ‖ξ‖
  let H : ℝ := ‖h3HeatFourierSymbol ν a ξ‖

  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity

  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity

  have hr : 0 ≤ r := by
    dsimp only [r]
    exact norm_nonneg _

  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact norm_nonneg _

  have hH1 : H ≤ 1 := by
    dsimp only [H]
    exact norm_h3HeatFourierSymbol_le_one hν.le ha.le ξ

  have hMoment :
      r * H ≤ C := by
    have h :=
      h3HeatFourierMomentMultiplier_le_three
        hν ha 1 (by norm_num) ξ
    simpa only [pow_one, r, H, C] using h

  have hHsq : H ^ 2 ≤ H := by
    nlinarith

  have hHalfSq :
      (Real.sqrt r * H) ^ 2 ≤ C := by
    calc
      (Real.sqrt r * H) ^ 2
          =
        r * H ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hr]
      _ ≤ r * H := by
        exact mul_le_mul_of_nonneg_left hHsq hr
      _ ≤ C := hMoment

  have hHalf :
      Real.sqrt r * H ≤ Real.sqrt C := by
    have hCsq :
        (Real.sqrt C) ^ 2 = C :=
      Real.sq_sqrt hC
    have hsqrtr : 0 ≤ Real.sqrt r :=
      Real.sqrt_nonneg _
    have hsqrtC : 0 ≤ Real.sqrt C :=
      Real.sqrt_nonneg _
    have hleft : 0 ≤ Real.sqrt r * H :=
      mul_nonneg hsqrtr hH0
    nlinarith

  have hFactor :
      (B * r ^ 2) ^ ((1 : ℝ) / 4)
        =
      B ^ ((1 : ℝ) / 4) * Real.sqrt r := by
    rw [Real.mul_rpow hB (sq_nonneg r)]
    congr 1
    calc
      (r ^ 2) ^ ((1 : ℝ) / 4)
          =
        (r ^ (2 : ℝ)) ^ ((1 : ℝ) / 4) := by
          congr 1
          exact (Real.rpow_natCast r 2).symm
      _ =
        r ^ ((2 : ℝ) * ((1 : ℝ) / 4)) := by
          rw [← Real.rpow_mul hr]
      _ =
        r ^ ((1 : ℝ) / 2) := by
          congr 1
          ring
      _ = Real.sqrt r := by
          rw [Real.sqrt_eq_rpow]

  have hPoint :=
    norm_h3HeatFourierSymbol_add_sub_le_quarter
      hν.le ha.le hh ξ

  calc
    ‖h3HeatFourierSymbol ν (a + h) ξ -
        h3HeatFourierSymbol ν a ξ‖
        ≤
      (B * r ^ 2) ^ ((1 : ℝ) / 4) * H := by
        simpa only [B, r, H, mul_assoc] using hPoint
    _ =
      B ^ ((1 : ℝ) / 4) *
        (Real.sqrt r * H) := by
      rw [hFactor]
      ring
    _ ≤
      B ^ ((1 : ℝ) / 4) *
        Real.sqrt C := by
      exact
        mul_le_mul_of_nonneg_left
          hHalf
          (Real.rpow_nonneg hB _)
    _ =
      h3HeatQuarterIncrementCoefficient ν a h := by
      rfl

/-- Scalar weighted spectral H³ heat evolution is quarter-Hölder in the time
increment after any positive base heat time. -/
theorem norm_h3SpectralScalarHeatApplyNN_add_sub_le_quarter
    {ν : ℝ}
    (hν : 0 < ν)
    (a h : ℝ≥0)
    (ha : 0 < (a : ℝ))
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (a + h) G -
        h3SpectralScalarHeatApplyNN
          ν hν.le a G‖
      ≤
    h3HeatQuarterIncrementCoefficient
        ν (a : ℝ) (h : ℝ) *
      ‖G‖ := by
  unfold h3SpectralScalarHeatApplyNN

  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (h3HeatFrequencyApplyNN ν hν.le (a + h) G)
      (h3HeatFrequencyApplyNN ν hν.le a G),
    h3HeatFrequencyApplyNN_coeFn
      ν hν.le (a + h) G,
    h3HeatFrequencyApplyNN_coeFn
      ν hν.le a G
  ] with ξ hsub hah ha0

  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hah, ha0]

  have hsymbol :
      ‖h3HeatFourierSymbol ν ((a + h : ℝ≥0) : ℝ) ξ -
          h3HeatFourierSymbol ν (a : ℝ) ξ‖
        ≤
      h3HeatQuarterIncrementCoefficient
        ν (a : ℝ) (h : ℝ) := by
    rw [NNReal.coe_add]
    exact
      norm_h3HeatFourierSymbol_add_sub_le_quarter_uniform
        (ν := ν) (a := (a : ℝ)) (h := (h : ℝ))
        hν ha h.property ξ

  rw [← sub_mul, norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      hsymbol
      (norm_nonneg _)

/-- Three-component weighted spectral H³ heat evolution inherits the same
quarter-Hölder time-increment bound. -/
theorem norm_h3SpectralVelocityHeatApplyNN_add_sub_le_quarter
    {ν : ℝ}
    (hν : 0 < ν)
    (a h : ℝ≥0)
    (ha : 0 < (a : ℝ))
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (a + h) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le a U‖
      ≤
    h3HeatQuarterIncrementCoefficient
        ν (a : ℝ) (h : ℝ) *
      ‖U‖ := by
  have hCoeff :
      0 ≤
        h3HeatQuarterIncrementCoefficient
          ν (a : ℝ) (h : ℝ) := by
    exact
      h3HeatQuarterIncrementCoefficient_nonneg
        hν.le a.property h.property

  apply
    (pi_norm_le_iff_of_nonneg
      (mul_nonneg hCoeff (norm_nonneg U))).2
  intro j

  change
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (a + h) (U j) -
        h3SpectralScalarHeatApplyNN
          ν hν.le a (U j)‖
      ≤
    h3HeatQuarterIncrementCoefficient
        ν (a : ℝ) (h : ℝ) *
      ‖U‖

  calc
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (a + h) (U j) -
        h3SpectralScalarHeatApplyNN
          ν hν.le a (U j)‖
        ≤
      h3HeatQuarterIncrementCoefficient
          ν (a : ℝ) (h : ℝ) *
        ‖U j‖ :=
      norm_h3SpectralScalarHeatApplyNN_add_sub_le_quarter
        hν a h ha (U j)
    _ ≤
      h3HeatQuarterIncrementCoefficient
          ν (a : ℝ) (h : ℝ) *
        ‖U‖ := by
      exact
        mul_le_mul_of_nonneg_left
          (h3SpectralVelocity_coordinate_norm_le U j)
          hCoeff

end

end Euclidean
end Bridge
end PrimeTensor
