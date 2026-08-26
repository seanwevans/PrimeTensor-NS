import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedFrozenRetarded

/-!
# Selected quarter-Hölder forcing: frozen half-tail frequency integral

`Forcing.SelectedFrozenRetarded` identifies the source-time integral of the
frozen terminal contribution at each fixed frequency with the already-closed
heat-lag primitive.  `Forcing.SelectedFrozenMass` then controls the frequency
integral of exactly that primitive against the frozen terminal forcing mass.

This file composes those two statements.  The result is the full frozen
half-tail budget in the frequency-outer / source-time-inner order, with no
remaining pointwise heat estimate:

    ∫ ξ, ∫_{t/2}^t |ξ|² |H_{t-s}(ξ) N_t(ξ)| ds dξ
      ≤ ((2π)² ν)⁻¹ · 4 C_L1 A².

The next step can therefore be purely measure-theoretic: exchange the
nonnegative frequency and source-time integrals to obtain the order appearing
in the second-Duhamel formula.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedFrozenFrequencyIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The frozen terminal contribution on the half-tail, integrated first in
source time and then in frequency, is bounded by the viscosity-only primitive
coefficient times the selected forcing `L¹` mass budget. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_frequency_timeIntegral_le_selectedRestart
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
    (∫ ξ : H3FourierPoint3,
        ∫ s in (t / 2)..t,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      ≤
    (((2 * Real.pi) ^ 2 * ν)⁻¹) *
      (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hEq :
      (∫ ξ : H3FourierPoint3,
          ∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ *
                h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        (∫ q in (0 : ℝ)..(t / 2),
          ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖) *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
    apply integral_congr_ae
    filter_upwards with ξ
    exact
      h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeIntegral_eq
        hν U₀ hA hU₀ ht i ξ

  calc
    (∫ ξ : H3FourierPoint3,
        ∫ s in (t / 2)..t,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        (∫ q in (0 : ℝ)..(t / 2),
          ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖) *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := hEq
    _ ≤
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
      dsimp only [W]
      exact
        h3RawFinLerayOuterProductDivergence_frozenSecondMomentPrimitive_frequencyIntegral_le_selectedRestart
          hν U₀ hA hU₀ (by positivity : 0 ≤ t / 2) i

end

end Euclidean
end Bridge
end PrimeTensor
