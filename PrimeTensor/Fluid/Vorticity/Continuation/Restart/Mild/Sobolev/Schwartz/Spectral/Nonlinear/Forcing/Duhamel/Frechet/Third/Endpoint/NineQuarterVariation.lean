import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Third.Endpoint.NineQuarterHeat
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected

/-!
# Nine-quarter endpoint variation of the selected nonlinear forcing

`NineQuarterHeat` closes the fractional heat multiplier

    |ξ|^(9/4) |H_τ(ξ)|.

The selected restart path already supplies the terminal quarter-Hölder forcing
modulus

    ∫ |N(W(s),W(s)) - N(W(t),W(t))|
      <= K (t-s)^(1/4).

This file composes those two statements without yet normalizing the scalar
lag coefficient.  The result is the complete Fourier-space estimate for the
varying terminal source:

    ∫ |ξ|^(9/4) |H_{t-s}(ξ) (N_s(ξ)-N_t(ξ))|
      <=
    C_(9/4)(ν,t-s) K (t-s)^(1/4).

Thus the remaining step is purely one-dimensional: identify the right-hand
side with a constant multiple of `(t-s)^(-7/8)` and integrate it in source
time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdEndpointNineQuarterVariation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Scalar profile obtained by pairing the `9/4` heat multiplier with a
quarter-Hölder forcing difference. -/
noncomputable def h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile
    (ν t K s : ℝ) : ℝ :=
  h3HeatNineQuarterMomentCoefficient ν (t - s) *
    (K * (t - s) ^ ((1 : ℝ) / 4))

/-- The `9/4` cancellation profile is nonnegative on a positive terminal lag
when the Hölder coefficient is nonnegative. -/
theorem h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile_nonneg
    {ν t K s : ℝ}
    (hν : 0 ≤ ν)
    (hK : 0 ≤ K)
    (hs : s ≤ t) :
    0 ≤
      h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile
        ν t K s := by
  unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile
  have hτ : 0 ≤ t - s := sub_nonneg.mpr hs
  have hC :
      0 ≤ h3HeatNineQuarterMomentCoefficient ν (t - s) :=
    h3HeatNineQuarterMomentCoefficient_nonneg hν hτ
  have hPow :
      0 ≤ (t - s) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hτ _
  positivity

/-- Generic endpoint estimate: a quarter-Hölder forcing difference, after a
positive heat lag, gains `9/4` Fourier moments with the scalar cancellation
profile recorded above. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_nineQuarter_le_quarter
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
    h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile
      ν t K s := by
  have hτ : 0 < t - s := sub_pos.mpr hs.2

  let D : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
        h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ

  have hDs :
      Integrable
        (h3RawFinLerayOuterProductDivergence (U s) (V s) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable
      (U s) (V s) i

  have hDt :
      Integrable
        (h3RawFinLerayOuterProductDivergence (U t) (V t) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable
      (U t) (V t) i

  have hD :
      Integrable D (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hDs.sub hDt

  have hHeat :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
        ≤
      h3HeatNineQuarterMomentCoefficient ν (t - s) *
        (∫ ξ : H3FourierPoint3, ‖D ξ‖) :=
    h3HeatFourierSymbol_nineQuarter_norm_integral_le
      hν hτ D hD

  have hHolderAt :
      (∫ ξ : H3FourierPoint3, ‖D ξ‖)
        ≤
      K * (t - s) ^ ((1 : ℝ) / 4) := by
    simpa only [
      D,
      h3RawFinLerayOuterProductDivergenceEndpointDifferenceL1Mass
    ] using hHolder s hs

  have hCoeff0 :
      0 ≤ h3HeatNineQuarterMomentCoefficient ν (t - s) :=
    h3HeatNineQuarterMomentCoefficient_nonneg
      hν.le hτ.le

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (U s) (V s) i ξ -
              h3RawFinLerayOuterProductDivergence (U t) (V t) i ξ)‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖ := by
      rfl
    _ ≤
      h3HeatNineQuarterMomentCoefficient ν (t - s) *
        (∫ ξ : H3FourierPoint3, ‖D ξ‖) :=
      hHeat
    _ ≤
      h3HeatNineQuarterMomentCoefficient ν (t - s) *
        (K * (t - s) ^ ((1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hHolderAt hCoeff0
    _ =
      h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile
        ν t K s := by
      rfl

/-- Selected-restart specialization of the `9/4` endpoint variation estimate.
All abstract path assumptions have been discharged by the existing selected
quarter-Hölder forcing theorem. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_nineQuarter_le_selectedRestart
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
    h3NonlinearForcingHeatNineQuarterQuarterCancellationProfile
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
    h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_nineQuarter_le_quarter
      hν W W i hs hHolder

end
end Euclidean
end Bridge
end PrimeTensor
