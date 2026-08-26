import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.Increment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Moment.Smoothing

/-!
# Positive-lag quantitative heat increments in spectral H³

The pointwise quarter-Hölder multiplier estimate is sufficient for endpoint
cancellation.  On a strictly positive base heat lag we can prove something
stronger and easier to lift to the spectral H³ norm.

For `a > 0` and `h ≥ 0`,

    H_{a+h} - H_a = (H_h - 1) H_a.

The elementary estimate

    1 - exp(-x) ≤ sqrt x

costs one Fourier frequency.  The existing positive-time first-moment heat
bound then pays for exactly that frequency on `H_a`.

Consequently,

    ‖H_{a+h} G - H_a G‖_{H³}
      ≤ C(ν,a,h) ‖G‖_{H³},

where

    C(ν,a,h)
      = sqrt ((2π)^2 ν h) * (sqrt (ν (a/3)))⁻¹.

Thus the heat orbit is quantitatively `1/2`-Hölder in time once a positive
amount of heat time has elapsed.  The same estimate is lifted componentwise
to the three-component spectral velocity state.

On a terminal window with `h ≤ 1`, this stronger square-root rate will imply
the quarter-Hölder rate required by the second-derivative endpoint theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralPositiveLagHeatIncrement
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Elementary square-root envelope for the real heat decrement. -/
theorem h3_one_sub_exp_neg_le_sqrt
    {x : ℝ}
    (hx : 0 ≤ x) :
    1 - Real.exp (-x) ≤ Real.sqrt x := by
  have hlin :
      1 - Real.exp (-x) ≤ x := by
    have h := Real.one_sub_le_exp_neg x
    linarith

  have hs0 : 0 ≤ Real.sqrt x :=
    Real.sqrt_nonneg x
  have hsq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt hx

  by_cases hx1 : x ≤ 1
  · have hs1 : Real.sqrt x ≤ 1 := by
      nlinarith
    have hxs : x ≤ Real.sqrt x := by
      nlinarith
    exact le_trans hlin hxs
  · have h1x : 1 ≤ x := by
      exact le_of_lt (lt_of_not_ge hx1)
    have hunit :
        1 - Real.exp (-x) ≤ 1 := by
      have hexp : 0 ≤ Real.exp (-x) :=
        (Real.exp_pos _).le
      linarith
    have h1s : 1 ≤ Real.sqrt x := by
      nlinarith
    exact le_trans hunit h1s

/-- One heat step differs from the identity by at most the square root of the
parabolic frequency-time scale. -/
theorem norm_h3HeatFourierSymbol_sub_one_le_sqrt
    {ν h : ℝ}
    (hν : 0 ≤ ν)
    (hh : 0 ≤ h)
    (ξ : H3FourierPoint3) :
    ‖h3HeatFourierSymbol ν h ξ - 1‖
      ≤
    Real.sqrt
      ((2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2) := by
  let x : ℝ :=
    (2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2

  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity

  have hexp_le :
      Real.exp (-x) ≤ 1 := by
    calc
      Real.exp (-x)
          ≤ Real.exp 0 := by
            exact Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
      _ = 1 := Real.exp_zero

  have hs :=
    h3_one_sub_exp_neg_le_sqrt hx

  unfold h3HeatFourierSymbol
  change
    ‖Complex.ofReal
        (Real.exp
          (-((2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2))) -
        (1 : ℂ)‖
      ≤
    Real.sqrt
      ((2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2)

  rw [← Complex.ofReal_one]
  rw [← Complex.ofReal_sub]
  rw [Complex.norm_real, Real.norm_eq_abs]

  change
    |Real.exp (-x) - 1| ≤ Real.sqrt x

  rw [abs_of_nonpos (sub_nonpos.mpr hexp_le)]
  linarith

/-- Semigroup form of the square-root heat increment estimate. -/
theorem norm_h3HeatFourierSymbol_add_sub_le_sqrt
    {ν a h : ℝ}
    (hν : 0 ≤ ν)
    (_ha : 0 ≤ a)
    (hh : 0 ≤ h)
    (ξ : H3FourierPoint3) :
    ‖h3HeatFourierSymbol ν (a + h) ξ -
        h3HeatFourierSymbol ν a ξ‖
      ≤
    Real.sqrt
        ((2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2) *
      ‖h3HeatFourierSymbol ν a ξ‖ := by
  rw [h3HeatFourierSymbol_add]

  have hFactor :
      h3HeatFourierSymbol ν h ξ *
            h3HeatFourierSymbol ν a ξ -
          h3HeatFourierSymbol ν a ξ
        =
      (h3HeatFourierSymbol ν h ξ - 1) *
        h3HeatFourierSymbol ν a ξ := by
    ring

  rw [hFactor, norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (norm_h3HeatFourierSymbol_sub_one_le_sqrt
        hν hh ξ)
      (norm_nonneg _)

/-- Positive base lag converts the pointwise heat increment into a uniform
multiplier estimate. -/
theorem norm_h3HeatFourierSymbol_add_sub_le_positiveLag
    {ν a h : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hh : 0 ≤ h)
    (ξ : H3FourierPoint3) :
    ‖h3HeatFourierSymbol ν (a + h) ξ -
        h3HeatFourierSymbol ν a ξ‖
      ≤
    Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
      (Real.sqrt (ν * (a / 3)))⁻¹ := by
  have hBase :
      0 ≤ (2 * Real.pi) ^ 2 * ν * h := by
    positivity

  have hMoment :=
    h3HeatFourierMomentMultiplier_le_three
      hν ha 1 (by norm_num) ξ

  have hMoment1 :
      ‖ξ‖ * ‖h3HeatFourierSymbol ν a ξ‖
        ≤
      (Real.sqrt (ν * (a / 3)))⁻¹ := by
    simpa only [pow_one] using hMoment

  calc
    ‖h3HeatFourierSymbol ν (a + h) ξ -
        h3HeatFourierSymbol ν a ξ‖
        ≤
      Real.sqrt
          ((2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2) *
        ‖h3HeatFourierSymbol ν a ξ‖ :=
      norm_h3HeatFourierSymbol_add_sub_le_sqrt
        hν.le ha.le hh ξ
    _ =
      Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
        (‖ξ‖ * ‖h3HeatFourierSymbol ν a ξ‖) := by
      rw [
        show
          (2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2
            =
          ((2 * Real.pi) ^ 2 * ν * h) * ‖ξ‖ ^ 2 by
            ring
      ]
      rw [Real.sqrt_mul hBase]
      rw [Real.sqrt_sq (norm_nonneg ξ)]
      ring
    _ ≤
      Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
        (Real.sqrt (ν * (a / 3)))⁻¹ := by
      exact
        mul_le_mul_of_nonneg_left
          hMoment1
          (Real.sqrt_nonneg _)

/-- Quantitative positive-lag heat increment on one weighted spectral H³
scalar component. -/
theorem norm_h3SpectralScalarHeatApplyNN_add_sub_le_positiveLag
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
    (Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
      (Real.sqrt (ν * (a / 3)))⁻¹) * ‖G‖ := by
  have hC :
      0 ≤
        Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
          (Real.sqrt (ν * (a / 3)))⁻¹ := by
    positivity

  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (h3SpectralScalarHeatApplyNN
        ν hν.le (NNReal.mk (a + h) (add_nonneg ha.le hh)) G)
      (h3SpectralScalarHeatApplyNN
        ν hν.le (NNReal.mk a ha.le) G),
    h3HeatFrequencyApplyNN_coeFn
      ν hν.le (NNReal.mk (a + h) (add_nonneg ha.le hh)) G,
    h3HeatFrequencyApplyNN_coeFn
      ν hν.le (NNReal.mk a ha.le) G
  ] with ξ hsub hlong hshort

  unfold h3SpectralScalarHeatApplyNN at hsub ⊢
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hlong, hshort]
  simp only [NNReal.coe_mk]
  rw [← sub_mul, norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (norm_h3HeatFourierSymbol_add_sub_le_positiveLag
        hν ha hh ξ)
      (norm_nonneg _)

/-- Quantitative positive-lag heat increment on the three-component spectral
H³ velocity state. -/
theorem norm_h3SpectralVelocityHeatApplyNN_add_sub_le_positiveLag
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
    (Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
      (Real.sqrt (ν * (a / 3)))⁻¹) * ‖U‖ := by
  have hC :
      0 ≤
        Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
          (Real.sqrt (ν * (a / 3)))⁻¹ := by
    positivity

  apply
    (pi_norm_le_iff_of_nonneg
      (mul_nonneg hC (norm_nonneg U))).2

  intro j

  change
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk (a + h) (add_nonneg ha.le hh)) (U j) -
        h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk a ha.le) (U j)‖
      ≤
    (Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
      (Real.sqrt (ν * (a / 3)))⁻¹) * ‖U‖

  calc
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk (a + h) (add_nonneg ha.le hh)) (U j) -
        h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk a ha.le) (U j)‖
        ≤
      (Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
        (Real.sqrt (ν * (a / 3)))⁻¹) * ‖U j‖ :=
      norm_h3SpectralScalarHeatApplyNN_add_sub_le_positiveLag
        hν ha hh (U j)
    _ ≤
      (Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
        (Real.sqrt (ν * (a / 3)))⁻¹) * ‖U‖ := by
      exact
        mul_le_mul_of_nonneg_left
          (h3SpectralVelocity_coordinate_norm_le U j)
          hC

end

end Euclidean
end Bridge
end PrimeTensor
