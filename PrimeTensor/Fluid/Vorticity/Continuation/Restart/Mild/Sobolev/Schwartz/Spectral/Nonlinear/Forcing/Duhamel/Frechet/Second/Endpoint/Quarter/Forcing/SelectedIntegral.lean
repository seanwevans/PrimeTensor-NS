import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedAEMajorant

/-!
# Selected quarter-Hölder forcing: integrated second-moment endpoint bound

`Forcing.SelectedAEMajorant` puts the selected fixed-lag second Fourier
moment below the quarter-cancellation majorant almost everywhere on the open
terminal interval.  The majorant is already interval-integrable and its exact
integral is known.

This file performs the remaining scalar time-integration step.  The terminal
endpoint is harmless: the forcing difference vanishes exactly at `s = t`.
Thus the norm of the time integral of the selected second-moment profile is
bounded by the explicit quarter-power endpoint budget

    12 * ν⁻¹ * K_selected * (t-a)^(1/4).

No abstract Hölder or integrability hypothesis remains in this estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected quarter-cancelled second Fourier moment has the explicit
integrated endpoint budget on every positive terminal interval. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_intervalIntegral_le_quarter_selectedRestart
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖∫ s in a..t,
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
                h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖)‖
      ≤
    12 * ν⁻¹ *
        h3NonlinearForcingQuarterSelectedRestartLocalCoefficient ν A a t *
        (t - a) ^ ((1 : ℝ) / 4) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : ℝ → ℝ := fun s =>
    ∫ ξ : H3FourierPoint3,
      ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν (t - s) ξ *
          (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
            h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖

  let M : ℝ → ℝ :=
    h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
      ν t
      (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient ν A a t)

  have hAE :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo a t)),
        F s ≤ M s := by
    dsimp only [F, M, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_le_quarter_selectedRestart_ae
        hν U₀ hA hU₀ ha hat htR i

  rw [ae_restrict_iff' measurableSet_Ioo] at hAE

  have hPointwise :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.Ioc a t → ‖F s‖ ≤ M s := by
    filter_upwards [hAE] with s hsAE
    intro hs
    by_cases hst : s < t
    · have hsOpen : s ∈ Set.Ioo a t := ⟨hs.1, hst⟩
      have hF0 : 0 ≤ F s := by
        dsimp only [F]
        exact integral_nonneg (fun ξ => by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg hF0]
      exact hsAE hsOpen
    · have hst_eq : s = t := by
        exact le_antisymm hs.2 (le_of_not_gt hst)
      subst s
      dsimp only [F, M]
      unfold h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
      simp

  have hMajorantInt :
      IntervalIntegrable M volume a t := by
    dsimp only [M]
    exact
      h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant_intervalIntegrable_selectedRestart

  have hBound :
      ‖∫ s in a..t, F s‖
        ≤
      ∫ s in a..t, M s := by
    exact
      intervalIntegral.norm_integral_le_of_norm_le
        (le_of_lt hat)
        hPointwise
        hMajorantInt

  change
    ‖∫ s in a..t,
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              (h3RawFinLerayOuterProductDivergence
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ s)
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ s) i ξ -
                h3RawFinLerayOuterProductDivergence
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ t)
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ t) i ξ)‖)‖
      ≤
    12 * ν⁻¹ *
        h3NonlinearForcingQuarterSelectedRestartLocalCoefficient ν A a t *
        (t - a) ^ ((1 : ℝ) / 4)

  have hBound' :
      ‖∫ s in a..t,
          (∫ ξ : H3FourierPoint3,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ *
                (h3RawFinLerayOuterProductDivergence
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ s)
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ s) i ξ -
                  h3RawFinLerayOuterProductDivergence
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ t)
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ t) i ξ)‖)‖
        ≤
      ∫ s in a..t,
        h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
          ν t
          (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient ν A a t)
          s := by
    simpa only [F, M, W] using hBound

  exact
    hBound'.trans_eq
      (h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant_integral_selectedRestart
        (le_of_lt hat))

end

end Euclidean
end Bridge
end PrimeTensor
