import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentForcing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.SevenQuarterMajorant
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FiveQuarterMajorant

/-!
# Fréchet endpoint induction: generic heat moment lifting

The nonlinear half of the induction is now exponent-parametric:

    M_{q+1}(state) -> M_q(forcing).

This file abstracts the heat half.  If an incoming amplitude carries moment
`q`, and a positive heat lag supplies a bounded residual moment `r`, then the
heated amplitude carries moment `q+r`:

    M_q(F) -> M_{q+r}(H_τ F).

The proof only uses the generic radial identity

    w_{q+r} = w_q w_r.

The two residuals used by the actual bootstrap are then immediate
specializations:

    r = 7/4,    terminal kernel (t-s)^(-7/8),
    r = 5/4,    terminal kernel (t-s)^(-5/8).

Thus the endpoint recurrence no longer depends on named exponents such as
`15/4`, `19/4`, or `23/4`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentHeatLift
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Generic positive-lag heat lift: an integrable `q`-moment amplitude becomes
an integrable `(q+r)`-moment amplitude whenever the residual `r` heat
multiplier is uniformly bounded by a nonnegative constant `C`. -/
theorem h3HeatFourierSymbol_momentLift_integrable
    {q r ν τ C : ℝ}
    (hq : 0 ≤ q)
    (hr : 0 ≤ r)
    (hC : 0 ≤ C)
    (hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight r ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖
          ≤
        C)
    (F : H3FourierPoint3 → ℂ)
    (hF : Integrable F (volume : Measure H3FourierPoint3))
    (hFq :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierMomentWeight (q + r) ξ : ℝ) : ℂ) *
          (h3HeatFourierSymbol ν τ ξ * F ξ))
      (volume : Measure H3FourierPoint3) := by
  have hqr : 0 ≤ q + r := by
    linarith

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierMomentWeight (q + r) ξ : ℝ) : ℂ) *
            (h3HeatFourierSymbol ν τ ξ * F ξ))
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp
        (continuous_h3FourierMomentWeight hqr)).aestronglyMeasurable.mul
      ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
        hF.aestronglyMeasurable)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (h3FourierMomentWeight q ξ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hFq.const_mul C

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hQ0 :
      0 ≤ h3FourierMomentWeight q ξ :=
    h3FourierMomentWeight_nonneg q ξ

  have hQR0 :
      0 ≤ h3FourierMomentWeight (q + r) ξ :=
    h3FourierMomentWeight_nonneg (q + r) ξ

  have hTargetNonneg :
      0 ≤
        h3FourierMomentWeight (q + r) ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖ :=
    mul_nonneg hQR0 (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        C * (h3FourierMomentWeight q ξ * ‖F ξ‖) :=
    mul_nonneg hC
      (mul_nonneg hQ0 (norm_nonneg _))

  have hFactor :
      h3FourierMomentWeight (q + r) ξ
        =
      h3FourierMomentWeight q ξ *
        h3FourierMomentWeight r ξ :=
    h3FourierMomentWeight_add hq hr ξ

  have hBound :
      h3FourierMomentWeight (q + r) ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
        ≤
      C * (h3FourierMomentWeight q ξ * ‖F ξ‖) := by
    rw [norm_mul, hFactor]

    calc
      (h3FourierMomentWeight q ξ *
          h3FourierMomentWeight r ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        h3FourierMomentWeight q ξ *
          (h3FourierMomentWeight r ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        h3FourierMomentWeight q ξ * C * ‖F ξ‖ := by
        have hScaled :
            h3FourierMomentWeight q ξ *
                (h3FourierMomentWeight r ξ *
                  ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            h3FourierMomentWeight q ξ * C :=
          mul_le_mul_of_nonneg_left
            (hHeat ξ) hQ0
        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (h3FourierMomentWeight q ξ * ‖F ξ‖) := by
        ring

  simpa only [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hQR0,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Quantitative generic heat lift under the same residual multiplier bound. -/
theorem h3HeatFourierSymbol_momentLift_normIntegral_le
    {q r ν τ C : ℝ}
    (hq : 0 ≤ q)
    (hr : 0 ≤ r)
    (hC : 0 ≤ C)
    (hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight r ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖
          ≤
        C)
    (F : H3FourierPoint3 → ℂ)
    (hF : Integrable F (volume : Measure H3FourierPoint3))
    (hFq :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + r) ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      ≤
    C *
      (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ * ‖F ξ‖) := by
  have hqr : 0 ≤ q + r := by
    linarith

  have hComplex :=
    h3HeatFourierSymbol_momentLift_integrable
      hq hr hC hHeat F hF hFq

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (q + r) ξ *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hQR0 :
        ∀ ξ : H3FourierPoint3,
          0 ≤ h3FourierMomentWeight (q + r) ξ := by
      intro ξ
      exact h3FourierMomentWeight_nonneg (q + r) ξ

    simpa only [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (hQR0 _)
    ] using hComplex.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (h3FourierMomentWeight q ξ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hFq.const_mul C

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + r) ξ *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
          ≤
        C * (h3FourierMomentWeight q ξ * ‖F ξ‖) := by
    intro ξ

    have hQ0 :
        0 ≤ h3FourierMomentWeight q ξ :=
      h3FourierMomentWeight_nonneg q ξ

    have hFactor :
        h3FourierMomentWeight (q + r) ξ
          =
        h3FourierMomentWeight q ξ *
          h3FourierMomentWeight r ξ :=
      h3FourierMomentWeight_add hq hr ξ

    rw [norm_mul, hFactor]

    calc
      (h3FourierMomentWeight q ξ *
          h3FourierMomentWeight r ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        h3FourierMomentWeight q ξ *
          (h3FourierMomentWeight r ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        h3FourierMomentWeight q ξ * C * ‖F ξ‖ := by
        have hScaled :
            h3FourierMomentWeight q ξ *
                (h3FourierMomentWeight r ξ *
                  ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            h3FourierMomentWeight q ξ * C :=
          mul_le_mul_of_nonneg_left
            (hHeat ξ) hQ0
        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (h3FourierMomentWeight q ξ * ‖F ξ‖) := by
        ring

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + r) ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        C * (h3FourierMomentWeight q ξ * ‖F ξ‖) :=
      hIntegral
    _ =
      C *
        (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight q ξ * ‖F ξ‖) := by
      rw [integral_const_mul]

/-- Generic `7/4` heat lift on one positive source section. -/
theorem h3HeatFourierSymbol_addSevenQuarter_frequencyIntegral_le
    {q ν t s : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (hs : s < t)
    (F : H3FourierPoint3 → ℂ)
    (hF : Integrable F (volume : Measure H3FourierPoint3))
    (hFq :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + (7 : ℝ) / 4) ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
      ≤
    h3HeatSevenQuarterTerminalMajorant ν t s *
      (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ * ‖F ξ‖) := by
  have hτ : 0 < t - s :=
    sub_pos.mpr hs

  let C : ℝ :=
    h3HeatSevenQuarterMomentCoefficient ν (t - s)

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatSevenQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight ((7 : ℝ) / 4) ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ‖
          ≤
        C := by
    intro ξ
    dsimp only [C]
    simpa only [
      h3FourierMomentWeight,
      h3FourierSevenQuarterWeight
    ] using
      (norm_h3HeatFourierSymbol_sevenQuarter_le
        hν hτ ξ)

  have hBase :=
    h3HeatFourierSymbol_momentLift_normIntegral_le
      hq
      (by norm_num : 0 ≤ (7 : ℝ) / 4)
      hC0
      hHeat
      F hF hFq

  have hCeq :
      C = h3HeatSevenQuarterTerminalMajorant ν t s := by
    dsimp only [C]
    exact
      h3HeatSevenQuarterMomentCoefficient_sub_eq_terminalMajorant
        hν hs

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + (7 : ℝ) / 4) ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
        ≤
      C *
        (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight q ξ * ‖F ξ‖) :=
      hBase
    _ =
      h3HeatSevenQuarterTerminalMajorant ν t s *
        (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight q ξ * ‖F ξ‖) := by
      rw [hCeq]

/-- Generic `5/4` heat lift on one positive source section. -/
theorem h3HeatFourierSymbol_addFiveQuarter_frequencyIntegral_le
    {q ν t s : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (hs : s < t)
    (F : H3FourierPoint3 → ℂ)
    (hF : Integrable F (volume : Measure H3FourierPoint3))
    (hFq :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + (5 : ℝ) / 4) ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
      ≤
    h3HeatFiveQuarterTerminalMajorant ν t s *
      (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ * ‖F ξ‖) := by
  have hτ : 0 < t - s :=
    sub_pos.mpr hs

  let C : ℝ :=
    h3HeatFiveQuarterMomentCoefficient ν (t - s)

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatFiveQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight ((5 : ℝ) / 4) ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ‖
          ≤
        C := by
    intro ξ
    dsimp only [C]
    simpa only [
      h3FourierMomentWeight,
      h3FourierFiveQuarterWeight
    ] using
      (norm_h3HeatFourierSymbol_fiveQuarter_le
        hν hτ ξ)

  have hBase :=
    h3HeatFourierSymbol_momentLift_normIntegral_le
      hq
      (by norm_num : 0 ≤ (5 : ℝ) / 4)
      hC0
      hHeat
      F hF hFq

  have hCeq :
      C = h3HeatFiveQuarterTerminalMajorant ν t s := by
    dsimp only [C]
    exact
      h3HeatFiveQuarterMomentCoefficient_sub_eq_terminalMajorant
        hν hs

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + (5 : ℝ) / 4) ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
        ≤
      C *
        (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight q ξ * ‖F ξ‖) :=
      hBase
    _ =
      h3HeatFiveQuarterTerminalMajorant ν t s *
        (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight q ξ * ‖F ξ‖) := by
      rw [hCeq]

end
end Euclidean
end Bridge
end PrimeTensor
