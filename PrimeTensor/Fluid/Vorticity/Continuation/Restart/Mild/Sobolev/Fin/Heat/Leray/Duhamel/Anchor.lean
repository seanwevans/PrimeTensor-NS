import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel.Right.Continuity

/-!
# Fixed-anchor approximation for the Fin-indexed H³ Duhamel map

For `0 ≤ a ≤ t`, the restart identity writes

    D(t) = H_{t-a} D(a) + tail(a,t-a).

The restart-tail estimate therefore gives

    ‖D(t) - H_{t-a} D(a)‖
      ≤ Cν sqrt(t-a) MU MV.

This is the exact approximation statement needed for the final positive-time
continuity proof: after choosing `a < t₀` close to `t₀`, the Duhamel map is
uniformly close near `t₀` to one fixed strongly-continuous heat orbit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/--
Fixed-anchor approximation of the variable-target Duhamel map by the heat
orbit launched from its value at the anchor time.
-/
theorem norm_h3SpectralFinHeatLerayDuhamel_sub_heat_restart_le
    {ν a t MU MV : ℝ}
    (hν : 0 < ν)
    (ha : 0 ≤ a)
    (hat : a ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    ‖h3SpectralFinHeatLerayDuhamel
          ν t hν U V
        -
      h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν)
        (NNReal.mk (t - a) (sub_nonneg.mpr hat))
        (h3SpectralFinHeatLerayDuhamel
          ν a hν U V)‖
      ≤
    h3HeatLerayDuhamelCoefficient ν *
      Real.sqrt (t - a) * MU * MV := by
  have hb : 0 ≤ t - a :=
    sub_nonneg.mpr hat

  have htime :
      a + (t - a) = t := by
    ring

  have hRestart :=
    h3SpectralFinHeatLerayDuhamel_add_time_of_continuous
      hν ha hb hMU hMV U V
      hUcont hVcont hU hV

  have hRestart' :
      h3SpectralFinHeatLerayDuhamel
          ν t hν U V
        =
      h3SpectralVelocityHeatApplyNN
          ν (le_of_lt hν)
          (NNReal.mk (t - a) hb)
          (h3SpectralFinHeatLerayDuhamel
            ν a hν U V)
        +
      ∫ s in a..t,
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V s := by
    simpa only [htime] using hRestart

  have hTail :=
    norm_h3SpectralFinHeatLerayDuhamel_tail_le
      (a := a)
      (b := t - a)
      (MU := MU)
      (MV := MV)
      hν hb hMU hMV U V
      hUcont hVcont hU hV

  have hTail' :
      ‖∫ s in a..t,
          h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s‖
        ≤
      h3HeatLerayDuhamelCoefficient ν *
        Real.sqrt (t - a) * MU * MV := by
    simpa only [htime] using hTail

  rw [hRestart']
  simpa only [add_sub_cancel_left] using hTail'

/--
Metric form of the fixed-anchor approximation.
-/
theorem dist_h3SpectralFinHeatLerayDuhamel_heat_restart_le
    {ν a t MU MV : ℝ}
    (hν : 0 < ν)
    (ha : 0 ≤ a)
    (hat : a ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    dist
      (h3SpectralFinHeatLerayDuhamel
        ν t hν U V)
      (h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν)
        (NNReal.mk (t - a) (sub_nonneg.mpr hat))
        (h3SpectralFinHeatLerayDuhamel
          ν a hν U V))
      ≤
    h3HeatLerayDuhamelCoefficient ν *
      Real.sqrt (t - a) * MU * MV := by
  rw [dist_eq_norm]
  exact
    norm_h3SpectralFinHeatLerayDuhamel_sub_heat_restart_le
      hν ha hat hMU hMV U V
      hUcont hVcont hU hV

end

end Euclidean
end Bridge
end PrimeTensor
