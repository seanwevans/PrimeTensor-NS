import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Third.Variation.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Second.Heat.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Third.Endpoint.NineQuarterMajorant
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Mild.Local
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected

/-!
# Positive-time monotonicity of endpoint coefficients

The remaining full-third bootstrap needs one numerical state envelope valid on
a whole positive interval.  The explicit pointwise envelopes already have the
right monotonic structure, but the relevant scalar facts were not yet named.

This file records exactly those facts:

* the second-moment heat coefficient decreases as the positive heat time grows;
* the `9/4` heat coefficient decreases as the positive heat time grows;
* the free-heat quarter-orbit coefficient decreases as the positive base time
  grows;
* the selected Duhamel quarter-Hölder coefficient increases with terminal
  time;
* consequently, enlarging a positive terminal interval can only increase the
  selected mild and selected forcing local quarter-Hölder coefficients.

The last theorem is the form needed repeatedly below:

    a ≤ r ≤ t
      ->
    K(ν,A,r/2,r) ≤ K(ν,A,a/2,t).

No PDE estimate is changed; these are scalar order lemmas for already-compiled
coefficients.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzPositiveTimeCoefficientMonotonicity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The quantitative second-moment heat coefficient is antitone on positive
heat times. -/
theorem h3HeatSecondMomentRawL1Coefficient_antitone_pos
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hab : a ≤ b) :
    h3HeatSecondMomentRawL1Coefficient ν b
      ≤
    h3HeatSecondMomentRawL1Coefficient ν a := by
  have hb : 0 < b :=
    lt_of_lt_of_le ha hab

  have hEa :
      h3HeatSecondMomentRawL1Coefficient ν a
        =
      3 * ν⁻¹ * a⁻¹ := by
    unfold h3HeatSecondMomentRawL1Coefficient
    have h :=
      h3NonlinearForcingHeatSecondMomentCoefficient_sq_eq
        (ν := ν) (t := a) (s := 0) hν ha
    simpa only [sub_zero] using h

  have hEb :
      h3HeatSecondMomentRawL1Coefficient ν b
        =
      3 * ν⁻¹ * b⁻¹ := by
    unfold h3HeatSecondMomentRawL1Coefficient
    have h :=
      h3NonlinearForcingHeatSecondMomentCoefficient_sq_eq
        (ν := ν) (t := b) (s := 0) hν hb
    simpa only [sub_zero] using h

  have hInv : b⁻¹ ≤ a⁻¹ :=
    inv_anti₀ ha hab

  rw [hEa, hEb]

  exact
    mul_le_mul_of_nonneg_left
      hInv
      (by positivity : 0 ≤ 3 * ν⁻¹)

/-- The interpolated `9/4` heat coefficient is antitone on positive heat
times. -/
theorem h3HeatNineQuarterMomentCoefficient_antitone_pos
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hab : a ≤ b) :
    h3HeatNineQuarterMomentCoefficient ν b
      ≤
    h3HeatNineQuarterMomentCoefficient ν a := by
  have hb : 0 < b :=
    lt_of_lt_of_le ha hab

  have hEa :=
    h3HeatNineQuarterMomentCoefficient_eq_secondMomentCoefficient_rpow
      hν ha

  have hEb :=
    h3HeatNineQuarterMomentCoefficient_eq_secondMomentCoefficient_rpow
      hν hb

  have hInv : b⁻¹ ≤ a⁻¹ :=
    inv_anti₀ ha hab

  have hBase :
      3 * ν⁻¹ * b⁻¹
        ≤
      3 * ν⁻¹ * a⁻¹ :=
    mul_le_mul_of_nonneg_left
      hInv
      (by positivity : 0 ≤ 3 * ν⁻¹)

  rw [hEa, hEb]

  exact
    Real.rpow_le_rpow
      (by positivity : 0 ≤ 3 * ν⁻¹ * b⁻¹)
      hBase
      (by norm_num : 0 ≤ (9 : ℝ) / 8)

/-- The selected free-heat quarter-orbit coefficient decreases when its
positive base time is moved forward. -/
theorem h3HeatQuarterOrbitCoefficient_antitone_pos
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hab : a ≤ b) :
    h3HeatQuarterOrbitCoefficient ν b
      ≤
    h3HeatQuarterOrbitCoefficient ν a := by
  have hb : 0 < b :=
    lt_of_lt_of_le ha hab

  have hArg :
      ν * (a / 3)
        ≤
      ν * (b / 3) := by
    nlinarith

  have hSqrt :
      Real.sqrt (ν * (a / 3))
        ≤
      Real.sqrt (ν * (b / 3)) :=
    Real.sqrt_le_sqrt hArg

  have hSqrtA :
      0 < Real.sqrt (ν * (a / 3)) :=
    Real.sqrt_pos.2 (by positivity)

  have hInv :
      (Real.sqrt (ν * (b / 3)))⁻¹
        ≤
      (Real.sqrt (ν * (a / 3)))⁻¹ :=
    inv_anti₀ hSqrtA hSqrt

  have hOuter :
      Real.sqrt ((Real.sqrt (ν * (b / 3)))⁻¹)
        ≤
      Real.sqrt ((Real.sqrt (ν * (a / 3)))⁻¹) :=
    Real.sqrt_le_sqrt hInv

  have hScale0 :
      0 ≤
        (((2 * Real.pi) ^ 2 * ν) ^ ((1 : ℝ) / 4)) :=
    Real.rpow_nonneg (by positivity) _

  unfold h3HeatQuarterOrbitCoefficient

  exact
    mul_le_mul_of_nonneg_left hOuter hScale0

/-- The selected Duhamel local quarter-Hölder coefficient is monotone in its
nonnegative terminal time. -/
theorem h3DuhamelQuarterSelectedRestartLocalCoefficient_mono
    {ν A s t : ℝ}
    (hν : 0 ≤ ν)
    (hA : 0 ≤ A)
    (hs : 0 ≤ s)
    (hst : s ≤ t) :
    h3DuhamelQuarterSelectedRestartLocalCoefficient ν A s
      ≤
    h3DuhamelQuarterSelectedRestartLocalCoefficient ν A t := by
  have h2A : 0 ≤ 2 * A := by
    positivity

  have hHistory :
      0 ≤
        h3DuhamelQuarterHistoryPowerCoefficient
          ν (2 * A) (2 * A) :=
    h3DuhamelQuarterHistoryPowerCoefficient_nonneg
      hν h2A h2A

  have hPower :
      s ^ ((1 : ℝ) / 4)
        ≤
      t ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hs hst (by norm_num)

  unfold h3DuhamelQuarterSelectedRestartLocalCoefficient

  exact
    add_le_add
      (mul_le_mul_of_nonneg_left
        hPower
        (by positivity :
          0 ≤
            4 *
              h3DuhamelQuarterHistoryPowerCoefficient
                ν (2 * A) (2 * A)))
      (le_refl _)

/-- Enlarging a positive terminal interval by moving its base backward and its
terminal time forward increases the selected mild quarter-Hölder coefficient. -/
theorem h3MildQuarterSelectedRestartLocalCoefficient_interval_mono
    {ν A a₀ a₁ t₁ t₀ : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha₀ : 0 < a₀)
    (haa : a₀ ≤ a₁)
    (ht₁ : 0 ≤ t₁)
    (htt : t₁ ≤ t₀) :
    h3MildQuarterSelectedRestartLocalCoefficient ν A a₁ t₁
      ≤
    h3MildQuarterSelectedRestartLocalCoefficient ν A a₀ t₀ := by
  have hHeat :=
    h3HeatQuarterOrbitCoefficient_antitone_pos
      hν ha₀ haa

  have hDuhamel :=
    h3DuhamelQuarterSelectedRestartLocalCoefficient_mono
      hν.le hA ht₁ htt

  unfold h3MildQuarterSelectedRestartLocalCoefficient

  exact
    add_le_add
      (mul_le_mul_of_nonneg_right hHeat hA)
      hDuhamel

/-- The same interval monotonicity after transferring the selected mild
quarter-Hölder coefficient to the nonlinear forcing. -/
theorem h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_interval_mono
    {ν A a₀ a₁ t₁ t₀ : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha₀ : 0 < a₀)
    (haa : a₀ ≤ a₁)
    (ht₁ : 0 ≤ t₁)
    (htt : t₁ ≤ t₀) :
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
        ν A a₁ t₁
      ≤
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
        ν A a₀ t₀ := by
  have hMild :=
    h3MildQuarterSelectedRestartLocalCoefficient_interval_mono
      hν hA ha₀ haa ht₁ htt

  have hScale0 :
      0 ≤ 4 * h3NonlinearForcingL1Coefficient * A := by
    have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
      h3NonlinearForcingL1Coefficient_nonneg
    positivity

  unfold h3NonlinearForcingQuarterSelectedRestartLocalCoefficient

  exact
    mul_le_mul_of_nonneg_left hMild hScale0

/-- Canonical half-interval specialization: for `a ≤ r ≤ t`, the local
quarter-Hölder forcing coefficient used by the `r`-terminal split is bounded
by the one coefficient attached to the larger interval `(a/2,t)`. -/
theorem h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_halfInterval_le
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
        ν A (r / 2) r
      ≤
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
        ν A (a / 2) t := by
  apply
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_interval_mono
      hν hA
  · positivity
  · linarith
  · exact le_trans ha.le har
  · exact hrt

end
end Euclidean
end Bridge
end PrimeTensor
