import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedFrozenMass

/-!
# Selected quarter-Hölder forcing: frozen retarded half-tail

`Forcing.SelectedFrozenMass` controls the fixed-frequency heat primitive after
lag integration.  The frozen terminal contribution in the actual Duhamel tail
is written in source time `s`, with lag `t - s`, on `t/2..t`.

This file performs only that retarded-time change of variables.  For every
fixed frequency the frozen half-tail integral is exactly the lag primitive on
`0..t/2`, multiplied by the terminal forcing norm.  Consequently it inherits
the viscosity-only pointwise primitive bound.

The next step can therefore address only the time/frequency Fubini exchange;
no further endpoint or heat-kernel algebra is needed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedFrozenRetarded
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At fixed frequency, the terminal forcing frozen on the half-tail
`t/2..t` becomes the heat-lag primitive on `0..t/2`. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeIntegral_eq
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (_ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ s in (t / 2)..t,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      =
    (∫ q in (0 : ℝ)..(t / 2),
        ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖) *
      ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Nξ : ℂ :=
    h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ

  have hReverse :
      (∫ s in (t / 2)..t,
          ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - s) ξ‖)
        =
      ∫ q in (0 : ℝ)..(t / 2),
        ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖ := by
    convert
      (intervalIntegral.integral_comp_sub_left
        (a := t / 2)
        (b := t)
        (fun q : ℝ => ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖)
        t) using 1 <;> ring

  calc
    (∫ s in (t / 2)..t,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * Nξ‖)
        =
      ∫ s in (t / 2)..t,
        (‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - s) ξ‖) * ‖Nξ‖ := by
          apply intervalIntegral.integral_congr
          intro s _hs
          change
            ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - s) ξ * Nξ‖ =
              (‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - s) ξ‖) * ‖Nξ‖
          simp only [norm_mul, mul_assoc]
    _ =
      (∫ s in (t / 2)..t,
          ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - s) ξ‖) * ‖Nξ‖ := by
          rw [intervalIntegral.integral_mul_const]
    _ =
      (∫ q in (0 : ℝ)..(t / 2),
          ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖) * ‖Nξ‖ := by
          rw [hReverse]
    _ =
      (∫ q in (0 : ℝ)..(t / 2),
          ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖) *
        ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
          rfl

/-- The fixed-frequency frozen half-tail is bounded by the viscosity-only heat
primitive coefficient times the terminal forcing norm. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeIntegral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ s in (t / 2)..t,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      ≤
    (((2 * Real.pi) ^ 2 * ν)⁻¹) *
      ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hEq :=
    h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeIntegral_eq
      hν U₀ hA hU₀ ht i ξ

  have hPrimitive :
      (∫ q in (0 : ℝ)..(t / 2),
          ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖)
        ≤
      ((2 * Real.pi) ^ 2 * ν)⁻¹ :=
    h3HeatFourierSymbol_secondMoment_timeIntegral_le
      hν (by positivity : 0 ≤ t / 2) ξ

  rw [hEq]
  exact
    mul_le_mul_of_nonneg_right
      hPrimitive
      (norm_nonneg _)

end

end Euclidean
end Bridge
end PrimeTensor
