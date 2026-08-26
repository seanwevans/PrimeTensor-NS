import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedFrozenFubini

/-!
# Selected quarter-Hölder forcing: frozen half-tail time integrability

`Forcing.SelectedFrozenFubini` proves genuine product integrability for the
nonnegative frozen terminal second-moment kernel on

    H3FourierPoint3 × (t/2,t).

This file extracts the time-side consequence needed for honest interval
recombination: after integrating in frequency, the frozen terminal profile is
itself interval-integrable on `t/2..t`.

The proof uses `Integrable.integral_prod_right` on the already-closed product
integrability theorem and then identifies the open and half-open interval
restrictions, which differ only at the endpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedFrozenTimeIntegrable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The frequency-integrated frozen terminal second-moment profile is
genuinely interval-integrable on the canonical terminal half-interval. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeFrequencyProfile_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntervalIntegrable
      (fun s : ℝ =>
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      volume
      (t / 2)
      t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : H3FourierPoint3 × ℝ → ℝ :=
    fun p =>
      (‖p.1‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) *
        ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i p.1‖

  have hProd :
      Integrable
        f
        ((volume : Measure H3FourierPoint3).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_fubini_integrable
        hν U₀ hA hU₀ ht i

  have hTime :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3, f (ξ, s))
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) :=
    hProd.integral_prod_right

  have hhalf : t / 2 ≤ t := by
    linarith

  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf]
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]

  change
    Integrable
      (fun s : ℝ =>
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))

  simpa only [f, norm_mul, mul_assoc] using hTime

end

end Euclidean
end Bridge
end PrimeTensor
