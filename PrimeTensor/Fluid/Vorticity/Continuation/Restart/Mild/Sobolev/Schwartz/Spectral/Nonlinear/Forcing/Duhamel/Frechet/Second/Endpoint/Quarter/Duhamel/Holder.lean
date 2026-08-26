import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.Remainder

/-!
# Quarter-power form of the canonical Duhamel restart remainder

The canonical restart remainder already has the sharp square-root estimate

    ‖R(a,T)‖ ≤ C_D(ν) sqrt(T) M_U M_V.

On the canonical restart interval the elapsed duration is at most one.  Hence

    sqrt(T) = T^(1/2) ≤ T^(1/4),

so the nonlinear remainder automatically satisfies the weaker quarter-Hölder
modulus required by the endpoint cancellation layer.

This file records that conversion separately from the later mild-path
bookkeeping.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open scoped NNReal

noncomputable section

/-- On `[0,1]`, the square-root gain dominates the weaker quarter-power gain. -/
theorem Real.sqrt_le_quarter_rpow_of_nonneg_of_le_one
    {x : ℝ}
    (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    Real.sqrt x ≤ x ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow]
  exact
    Real.rpow_le_rpow_of_exponent_ge'
      hx0 hx1 (by norm_num) (by norm_num)

/-- The canonical restart radius never exceeds one. -/
theorem h3FinHeatLerayRestartRadius_le_one
    (ν : ℝ)
    {A : ℝ}
    (hA : 0 ≤ A) :
    h3FinHeatLerayRestartRadius ν A ≤ 1 := by
  have hscale : 0 ≤ h3FinHeatLerayRestartScale ν A :=
    h3FinHeatLerayRestartScale_nonneg ν hA
  have hden : 0 < h3FinHeatLerayRestartScale ν A + 1 := by
    linarith
  have hinv0 :
      0 ≤ 1 / (h3FinHeatLerayRestartScale ν A + 1) :=
    (one_div_pos.mpr hden).le
  have hinv1 :
      1 / (h3FinHeatLerayRestartScale ν A + 1) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    linarith
  unfold h3FinHeatLerayRestartRadius
  nlinarith

/-- Time-independent coefficient for the quarter-power selected-restart
Duhamel remainder estimate. -/
noncomputable def h3DuhamelQuarterSelectedRestartCoefficient
    (ν A : ℝ) : ℝ :=
  h3HeatLerayDuhamelPathCoefficient ν * (2 * A) * (2 * A)

/-- The selected-restart Duhamel quarter coefficient is nonnegative for a
nonnegative H³ radius. -/
theorem h3DuhamelQuarterSelectedRestartCoefficient_nonneg
    (ν : ℝ)
    {A : ℝ}
    (hA : 0 ≤ A) :
    0 ≤ h3DuhamelQuarterSelectedRestartCoefficient ν A := by
  unfold h3DuhamelQuarterSelectedRestartCoefficient
  exact
    mul_nonneg
      (mul_nonneg
        (h3HeatLerayDuhamelPathCoefficient_nonneg ν)
        (mul_nonneg (by norm_num) hA))
      (mul_nonneg (by norm_num) hA)

/-- On elapsed durations at most one, the selected canonical restart remainder
has an explicit quarter-power modulus. -/
theorem norm_h3SpectralFinHeatLerayDuhamelRestartRemainder_selectedRestart_le_quarter
    {ν A a : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (T : NNReal)
    (hT1 : (T : ℝ) ≤ 1) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν a hν W W T‖
      ≤
    h3DuhamelQuarterSelectedRestartCoefficient ν A *
      (T : ℝ) ^ ((1 : ℝ) / 4) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hBase :
      ‖h3SpectralFinHeatLerayDuhamelRestartRemainder
          ν a hν W W T‖
        ≤
      h3HeatLerayDuhamelPathCoefficient ν *
        Real.sqrt (T : ℝ) * (2 * A) * (2 * A) := by
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayDuhamelRestartRemainder_selectedRestart_le
        hν U₀ hA hU₀ T

  have hsqrt :
      Real.sqrt (T : ℝ) ≤
        (T : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.sqrt_le_quarter_rpow_of_nonneg_of_le_one
      T.property hT1

  have hK :
      0 ≤ h3DuhamelQuarterSelectedRestartCoefficient ν A :=
    h3DuhamelQuarterSelectedRestartCoefficient_nonneg ν hA.le

  change
    ‖h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν a hν W W T‖
      ≤
    h3DuhamelQuarterSelectedRestartCoefficient ν A *
      (T : ℝ) ^ ((1 : ℝ) / 4)

  calc
    ‖h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν a hν W W T‖
        ≤
      h3HeatLerayDuhamelPathCoefficient ν *
        Real.sqrt (T : ℝ) * (2 * A) * (2 * A) := hBase
    _ =
      h3DuhamelQuarterSelectedRestartCoefficient ν A *
        Real.sqrt (T : ℝ) := by
      unfold h3DuhamelQuarterSelectedRestartCoefficient
      ring
    _ ≤
      h3DuhamelQuarterSelectedRestartCoefficient ν A *
        (T : ℝ) ^ ((1 : ℝ) / 4) := by
      exact mul_le_mul_of_nonneg_left hsqrt hK

/-- Canonical-radius form: no separate unit-duration hypothesis is needed. -/
theorem norm_h3SpectralFinHeatLerayDuhamelRestartRemainder_selectedRestart_le_quarter_of_le_restartRadius
    {ν A a : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (T : NNReal)
    (hTR : (T : ℝ) ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν a hν W W T‖
      ≤
    h3DuhamelQuarterSelectedRestartCoefficient ν A *
      (T : ℝ) ^ ((1 : ℝ) / 4) := by
  have hT1 : (T : ℝ) ≤ 1 :=
    le_trans hTR (h3FinHeatLerayRestartRadius_le_one ν hA.le)
  exact
    norm_h3SpectralFinHeatLerayDuhamelRestartRemainder_selectedRestart_le_quarter
      hν U₀ hA hU₀ T hT1

end

end Euclidean
end Bridge
end PrimeTensor
