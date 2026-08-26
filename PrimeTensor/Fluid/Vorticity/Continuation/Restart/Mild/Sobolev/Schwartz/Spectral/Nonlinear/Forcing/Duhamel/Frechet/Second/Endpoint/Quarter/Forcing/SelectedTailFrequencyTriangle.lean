import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedTailTriangle

/-!
# Selected quarter-Hölder forcing: frequency-integrated terminal-tail split

`Forcing.SelectedTailTriangle` gives the pointwise frequency inequality that
splits the unsimplified terminal forcing into its endpoint-cancelled and
terminally frozen pieces.

This file pushes that triangle inequality through the Fourier integral at one
strictly retarded source time.  Positive lag makes all three second-moment
frequency profiles integrable.  The result is the exact scalar split needed
before integrating over the terminal half of the Duhamel time interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedTailFrequencyTriangle
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strict retarded source time, the frequency-integrated unsplit
second moment is bounded by the sum of the endpoint-cancelled and frozen
frequency integrals. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_secondMoment_frequencyIntegral_le_endpointDifference_add_frozen
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (W : ℝ → H3SpectralFinVectorState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)
      ≤
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖) +
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
  have hτ : 0 < t - s := sub_pos.mpr hs

  let F : H3FourierPoint3 → ℝ := fun ξ =>
    ‖ξ‖ ^ 2 *
      ‖h3HeatFourierSymbol ν (t - s) ξ *
        h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖

  let D : H3FourierPoint3 → ℝ := fun ξ =>
    ‖ξ‖ ^ 2 *
      ‖h3HeatFourierSymbol ν (t - s) ξ *
        (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
          h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖

  let G : H3FourierPoint3 → ℝ := fun ξ =>
    ‖ξ‖ ^ 2 *
      ‖h3HeatFourierSymbol ν (t - s) ξ *
        h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖

  have hFInt : Integrable F (volume : Measure H3FourierPoint3) := by
    dsimp only [F]
    simpa only [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
    ] using
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ (W s) (W s) i 2 (by norm_num))

  have hGInt : Integrable G (volume : Measure H3FourierPoint3) := by
    dsimp only [G]
    simpa only [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
    ] using
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ (W t) (W t) i 2 (by norm_num))

  have hRawS :
      Integrable
        (h3RawFinLerayOuterProductDivergence (W s) (W s) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable (W s) (W s) i

  have hRawT :
      Integrable
        (h3RawFinLerayOuterProductDivergence (W t) (W t) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable (W t) (W t) i

  have hDMeas :
      AEStronglyMeasurable D (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      ((continuous_norm.pow 2).aestronglyMeasurable).mul
        ((continuous_h3HeatFourierSymbol ν (t - s)).aestronglyMeasurable.mul
          (hRawS.sub hRawT).aestronglyMeasurable).norm

  have hDInt : Integrable D (volume : Measure H3FourierPoint3) := by
    refine (hFInt.add hGInt).mono' hDMeas ?_
    filter_upwards with ξ
    have hD0 : 0 ≤ D ξ := by
      dsimp only [D]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hD0]
    dsimp only [F, D, G]
    have hTri :
        ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖
          ≤
        ‖h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖ +
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
      rw [mul_sub]
      exact norm_sub_le _ _
    calc
      ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖
          ≤
        ‖ξ‖ ^ 2 *
          (‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖ +
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖) := by
            exact mul_le_mul_of_nonneg_left hTri (sq_nonneg ‖ξ‖)
      _ =
        ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖ +
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
            ring

  rw [← integral_add hDInt hGInt]
  refine integral_mono_ae hFInt (hDInt.add hGInt) ?_
  filter_upwards with ξ
  simpa only [F, D, G] using
    (h3RawFinLerayOuterProductDivergenceHeat_secondMoment_le_endpointDifference_add_frozen
      ν t s W i ξ)

end

end Euclidean
end Bridge
end PrimeTensor
