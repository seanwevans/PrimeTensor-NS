import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedHead

/-!
# Selected quarter-Hölder forcing: uniform half-head bound

`Forcing.SelectedHead` isolates the old half of the Duhamel interval, where
all retarded heat lags are bounded below by `t / 2`.  This file turns that
geometric separation into a quantitative second-Fourier-moment bound.

The key point is to avoid comparing inverse powers of the lag directly.
For `s ≤ t/2`, write

    t - s = t/2 + ((t-s) - t/2).

The heat semigroup factors accordingly.  The extra nonnegative heat factor is
a contraction, so the second moment at lag `t-s` is dominated by the same
second moment at the fixed lag `t/2`.  The selected-path raw forcing `L¹`
bound then supplies a single coefficient valid on the whole head.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedHeadBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fixed positive-lag second Fourier moment of one heat-smoothed raw forcing
coordinate, bounded by the raw Fourier `L¹` mass. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_secondMoment_integral_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν τ ξ *
            h3RawFinLerayOuterProductDivergence U V i ξ‖)
      ≤
    ((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 2 *
      h3RawFinLerayOuterProductDivergenceL1Mass U V i := by
  let C : ℝ := (Real.sqrt (ν * (τ / 3)))⁻¹

  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν τ ξ *
              h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
    ] using
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ U V i 2 (by norm_num))

  have hRawInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergence_integrable U V i).norm

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRawInt.const_mul (C ^ 2)

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν τ ξ *
            h3RawFinLerayOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        C ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
      refine integral_mono_ae hTargetInt hMajorantInt ?_
      filter_upwards with ξ
      have hMoment :=
        h3HeatFourierMomentMultiplier_le_three
          hν hτ 2 (by norm_num) ξ
      rw [norm_mul]
      calc
        ‖ξ‖ ^ 2 *
            (‖h3HeatFourierSymbol ν τ ξ‖ *
              ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
            =
          (‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν τ ξ‖) *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
              ring
        _ ≤
          C ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
          dsimp only [C]
          exact
            mul_le_mul_of_nonneg_right
              hMoment
              (norm_nonneg _)
    _ =
      C ^ 2 *
        h3RawFinLerayOuterProductDivergenceL1Mass U V i := by
      unfold h3RawFinLerayOuterProductDivergenceL1Mass
      rw [integral_const_mul]
    _ =
      ((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 2 *
        h3RawFinLerayOuterProductDivergenceL1Mass U V i := by
      rfl

/-- Uniform coefficient for the selected second-moment forcing on the old
half-head.  It uses only the fixed lag `t/2` and the global selected-path raw
forcing mass bound. -/
noncomputable def h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
    (ν A t : ℝ) : ℝ :=
  ((Real.sqrt (ν * ((t / 2) / 3)))⁻¹) ^ 2 *
    (4 * h3NonlinearForcingL1Coefficient * A ^ 2)

/-- On the canonical old head `0..t/2`, the selected heat-smoothed forcing
second moment is bounded by one coefficient independent of the source time. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_secondMoment_le_quarter_selectedRestart_halfHead
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hs : s ∈ Set.Icc (0 : ℝ) (t / 2))
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)
      ≤
    h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
      ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have htHalf : 0 < t / 2 := by
    positivity

  have hLag : t / 2 ≤ t - s :=
    h3Quarter_halfTime_le_retardedLag hs.2

  have hExtra : 0 ≤ (t - s) - t / 2 :=
    sub_nonneg.mpr hLag

  have hslt : s < t := by
    have hhalfLt : t / 2 < t := by
      linarith
    exact lt_of_le_of_lt hs.2 hhalfLt

  have hτ : 0 < t - s :=
    sub_pos.mpr hslt

  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_secondMoment_integrable_quarter_selectedRestart_halfHead
        hν U₀ hA hU₀ ht hs i

  have hHalfInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t / 2) ξ *
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
    ] using
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν htHalf (W s) (W s) i 2 (by norm_num))

  have hLagCompare :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t / 2) ξ *
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖ := by
    refine integral_mono_ae hTargetInt hHalfInt ?_
    filter_upwards with ξ

    have hsplit :
        t / 2 + ((t - s) - t / 2) = t - s := by
      ring

    have hheat :
        h3HeatFourierSymbol ν (t - s) ξ
          =
        h3HeatFourierSymbol ν ((t - s) - t / 2) ξ *
          h3HeatFourierSymbol ν (t / 2) ξ := by
      simpa only [hsplit] using
        (h3HeatFourierSymbol_add ν (t / 2) ((t - s) - t / 2) ξ)

    have hcontract :
        ‖h3HeatFourierSymbol ν ((t - s) - t / 2) ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one hν.le hExtra ξ

    rw [hheat]
    have hprod :
        ‖(h3HeatFourierSymbol ν ((t - s) - t / 2) ξ *
              h3HeatFourierSymbol ν (t / 2) ξ) *
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖
          ≤
        ‖h3HeatFourierSymbol ν (t / 2) ξ *
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖ := by
      rw [mul_assoc, norm_mul]
      exact
        mul_le_of_le_one_left
          (norm_nonneg _)
          hcontract

    exact
      mul_le_mul_of_nonneg_left
        hprod
        (pow_nonneg (norm_nonneg _) 2)

  have hHalfBound :=
    h3RawFinLerayOuterProductDivergenceHeat_secondMoment_integral_le
      hν htHalf (W s) (W s) i

  have hMass :=
    h3RawFinLerayOuterProductDivergenceL1Mass_selectedRestart_le
      hν U₀ hA hU₀ s i

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t / 2) ξ *
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖ :=
      hLagCompare
    _ ≤
      ((Real.sqrt (ν * ((t / 2) / 3)))⁻¹) ^ 2 *
        h3RawFinLerayOuterProductDivergenceL1Mass (W s) (W s) i :=
      hHalfBound
    _ ≤
      ((Real.sqrt (ν * ((t / 2) / 3)))⁻¹) ^ 2 *
        (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
      exact
        mul_le_mul_of_nonneg_left
          hMass
          (sq_nonneg _)
    _ =
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
        ν A t := by
      rfl

end

end Euclidean
end Bridge
end PrimeTensor
