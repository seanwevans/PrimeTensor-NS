import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedHeadMajorantIntegral

/-!
# Selected quarter-Hölder forcing: integrated half-head bound

`Forcing.SelectedHeadBound` gives a pointwise second-Fourier-moment estimate
on the canonical old half-head `0..t/2`, while
`Forcing.SelectedHeadMajorantIntegral` records the exact integral of the
corresponding constant scalar majorant.

This file transfers the actual selected head profile under the time integral.
The result is the explicit old-history budget

    ‖∫₀^{t/2} secondMoment(s) ds‖
      ≤ (t/2) * C_head(ν,A,t).

Together with the quarter-cancelled terminal-half estimate, this is the last
scalar integration step needed before recombining the two halves of the
selected second-Duhamel forcing interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedHeadIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected heat-smoothed raw forcing on the canonical old half-head has
an explicit integrated second-Fourier-moment budget. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeat_secondMoment_intervalIntegral_le_quarter_selectedRestart_halfHead
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
    ‖∫ s in (0 : ℝ)..(t / 2),
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)‖
      ≤
    (t / 2) *
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
        ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : ℝ → ℝ := fun s =>
    ∫ ξ : H3FourierPoint3,
      ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν (t - s) ξ *
          h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖

  let M : ℝ → ℝ :=
    h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant
      ν A t

  have htHalf0 : 0 ≤ t / 2 := by
    positivity

  have hPointwise :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.Ioc (0 : ℝ) (t / 2) → ‖F s‖ ≤ M s := by
    filter_upwards with s
    intro hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) (t / 2) :=
      ⟨le_of_lt hs.1, hs.2⟩
    have hFBound :=
      h3RawFinLerayOuterProductDivergenceHeat_secondMoment_le_quarter_selectedRestart_halfHead
        hν U₀ hA hU₀ ht hsIcc i
    have hF0 : 0 ≤ F s := by
      dsimp only [F]
      exact integral_nonneg (fun ξ => by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hF0]
    simpa only [F, M, W,
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant] using hFBound

  have hMajorantInt :
      IntervalIntegrable M volume (0 : ℝ) (t / 2) := by
    dsimp only [M]
    exact
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant_intervalIntegrable

  have hBound :
      ‖∫ s in (0 : ℝ)..(t / 2), F s‖
        ≤
      ∫ s in (0 : ℝ)..(t / 2), M s := by
    exact
      intervalIntegral.norm_integral_le_of_norm_le
        htHalf0
        hPointwise
        hMajorantInt

  change
    ‖∫ s in (0 : ℝ)..(t / 2),
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ s)
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ s) i ξ‖)‖
      ≤
    (t / 2) *
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
        ν A t

  have hBound' :
      ‖∫ s in (0 : ℝ)..(t / 2),
          (∫ ξ : H3FourierPoint3,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ *
                h3RawFinLerayOuterProductDivergence
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ s)
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ s) i ξ‖)‖
        ≤
      ∫ s in (0 : ℝ)..(t / 2),
        h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant
          ν A t s := by
    simpa only [F, M, W] using hBound

  exact
    hBound'.trans_eq
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant_integral

end

end Euclidean
end Bridge
end PrimeTensor
