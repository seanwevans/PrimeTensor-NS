import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedTail

/-!
# Selected quarter-Hölder forcing: positive-lag half-head

`Forcing.SelectedTail` fixes the canonical positive-time split at `t / 2`.
On the complementary head `0..t/2`, every retarded heat lag is bounded away
from zero.  Consequently the raw nonlinear forcing can spend two Fourier
moments there using only the existing positive-time heat smoothing theorem;
no endpoint cancellation is needed.

This file records the two facts needed for the head side of the split:

* the selected diagonal raw forcing has a uniform explicit `L¹` bound; and
* every source time in the half-head has an integrable second Fourier moment
  after the retarded heat multiplier is applied.

The next layer can therefore bound and time-integrate the head using a fixed
positive-lag coefficient, independently of the terminal cancellation layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedHead
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Along the selected restart extension, one diagonal raw forcing coordinate
has a uniform Fourier `L¹` bound obtained from the global `2A` path bound. -/
theorem h3RawFinLerayOuterProductDivergenceL1Mass_selectedRestart_le
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (s : ℝ)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceL1Mass (W s) (W s) i
      ≤
    4 * h3NonlinearForcingL1Coefficient * A ^ 2 := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW : ‖W s‖ ≤ 2 * A := by
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
    h3NonlinearForcingL1Coefficient_nonneg

  have h2A : 0 ≤ 2 * A := by
    positivity

  calc
    h3RawFinLerayOuterProductDivergenceL1Mass (W s) (W s) i
        ≤
      h3NonlinearForcingL1Coefficient * ‖W s‖ * ‖W s‖ :=
      h3RawFinLerayOuterProductDivergenceL1Mass_le (W s) (W s) i
    _ ≤
      h3NonlinearForcingL1Coefficient * (2 * A) * (2 * A) := by
      exact
        mul_le_mul
          (mul_le_mul_of_nonneg_left hW hC)
          hW
          (norm_nonneg _)
          (mul_nonneg hC h2A)
    _ =
      4 * h3NonlinearForcingL1Coefficient * A ^ 2 := by
      ring

/-- On the canonical old head `0..t/2`, the selected forcing after retarded
heat has an integrable second Fourier moment.  This is purely a positive-lag
smoothing statement. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_secondMoment_integrable_quarter_selectedRestart_halfHead
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
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hslt : s < t := by
    have hhalf : t / 2 < t := by
      linarith
    exact lt_of_le_of_lt hs.2 hhalf

  have hτ : 0 < t - s := sub_pos.mpr hslt

  have hMoment :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
      hν hτ (W s) (W s) i 2 (by norm_num)

  simpa only [
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
  ] using hMoment

end

end Euclidean
end Bridge
end PrimeTensor
