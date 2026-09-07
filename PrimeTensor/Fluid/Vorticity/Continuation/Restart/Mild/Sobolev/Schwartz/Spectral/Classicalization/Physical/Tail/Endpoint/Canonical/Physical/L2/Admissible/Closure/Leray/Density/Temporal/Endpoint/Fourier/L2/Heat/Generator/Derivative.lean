import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Heat.Generator.Derivative.AtZero
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Heat.Semigroup
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Heat.Intertwining
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Physical L² temporal admissibility: heat-generator derivative on the half-line

The raw Fourier heat orbit now has the correct one-sided derivative at elapsed
time zero.  The semigroup law transports that result to every nonnegative base
time without repeating dominated convergence.

For `t ≤ y`, write `h = y - t`.  The semigroup law and exact H³ deweighting
give

    slope(S(·) raw(G), t, y)
      =
    Q_h(S_H3(t) G),

where `Q_h` is the zero-based quotient already controlled in
`FourierL2HeatGeneratorConvergence`.

Composing the zero-based quotient limit with `y ↦ y - t` therefore proves the
right derivative at every nonnegative elapsed time.  The derivative remains
explicitly on the weighted H³ generator domain.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatGeneratorDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The slope of the raw Fourier heat orbit at a nonnegative base time is the
zero-based heat quotient of the weighted state evolved to that base time. -/
theorem h3RawFourierL2HeatRealPath_slope_eq_quotient
    {ν t y : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (hy : t < y)
    (G : H3SpectralScalarState) :
    slope
        (h3RawFourierL2HeatRealPath ν hν G)
        t y
      =
    h3RawFourierL2HeatQuotientState
      ν (y - t) hν
      (h3SpectralScalarHeatApplyNN
        ν hν (Real.toNNReal t) G) := by
  have hy0 : 0 ≤ y :=
    ht.trans hy.le

  have hyt0 : 0 ≤ y - t :=
    sub_nonneg.mpr hy.le

  have hTimeAdd :
      Real.toNNReal y
        =
      Real.toNNReal t + Real.toNNReal (y - t) := by
    apply NNReal.eq
    calc
      (Real.toNNReal y : ℝ)
          = y :=
        Real.coe_toNNReal y hy0
      _ =
        t + (y - t) := by
          ring
      _ =
        (Real.toNNReal t : ℝ) +
          (Real.toNNReal (y - t) : ℝ) := by
            rw [
              Real.coe_toNNReal t ht,
              Real.coe_toNNReal (y - t) hyt0
            ]
      _ =
        ((Real.toNNReal t +
            Real.toNNReal (y - t) : ℝ≥0) : ℝ) := by
          rw [NNReal.coe_add]

  have hRawBase :=
    h3SpectralScalarRawFourierL2_heatApplyNN
      ν hν (Real.toNNReal t) G

  have hSemigroup :
      h3HeatFrequencyApplyNN
          ν hν
          (Real.toNNReal t + Real.toNNReal (y - t))
          (h3SpectralScalarRawFourierL2 G)
        =
      h3HeatFrequencyApplyNN
          ν hν (Real.toNNReal (y - t))
          (h3HeatFrequencyApplyNN
            ν hν (Real.toNNReal t)
            (h3SpectralScalarRawFourierL2 G)) := by
    simpa only [h3SpectralScalarHeatApplyNN] using
      h3SpectralScalarHeatApplyNN_add_time
        ν hν
        (Real.toNNReal t)
        (Real.toNNReal (y - t))
        (h3SpectralScalarRawFourierL2 G)

  rw [slope_def_module]

  unfold h3RawFourierL2HeatRealPath
  unfold h3RawFourierL2HeatQuotientState

  rw [hRawBase]
  rw [hTimeAdd]
  rw [hSemigroup]

/-- At every nonnegative elapsed time, the quotient-safe raw Fourier heat orbit
has right derivative equal to viscosity times the raw Fourier Laplacian of the
weighted heat-evolved state. -/
theorem h3RawFourierL2HeatRealPath_hasDerivWithinAt_right
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (G : H3SpectralScalarState) :
    HasDerivWithinAt
      (h3RawFourierL2HeatRealPath
        ν hν G)
      (h3RawFourierL2HeatGeneratorState
        ν
        (h3SpectralScalarHeatApplyNN
          ν hν (Real.toNNReal t) G))
      (Set.Ioi t)
      t := by
  refine
    (hasDerivWithinAt_iff_tendsto_slope'
      (f := h3RawFourierL2HeatRealPath ν hν G)
      (f' :=
        h3RawFourierL2HeatGeneratorState
          ν
          (h3SpectralScalarHeatApplyNN
            ν hν (Real.toNNReal t) G))
      (s := Set.Ioi t)
      (x := t)
      (by simp)).2 ?_

  let H : H3SpectralScalarState :=
    h3SpectralScalarHeatApplyNN
      ν hν (Real.toNNReal t) G

  have hShift :
      Tendsto
        (fun y : ℝ => y - t)
        (𝓝[Set.Ioi t] t)
        (𝓝[Set.Ioi (0 : ℝ)] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hBase :
          Tendsto
            (fun y : ℝ => y - t)
            (𝓝 t)
            (𝓝 (0 : ℝ)) := by
        simpa using
          (tendsto_id.sub_const t :
            Tendsto
              (fun y : ℝ => y - t)
              (𝓝 t)
              (𝓝 (t - t)))
      exact
        hBase.mono_left
          (show
            (𝓝[Set.Ioi t] t) ≤ (𝓝 t) by
              exact inf_le_left)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.mpr (Set.mem_Ioi.mp hy)

  have hConv :
      Tendsto
        (fun y : ℝ =>
          h3RawFourierL2HeatQuotientState
            ν (y - t) hν H)
        (𝓝[Set.Ioi t] t)
        (𝓝
          (h3RawFourierL2HeatGeneratorState
            ν H)) :=
    (tendsto_h3RawFourierL2HeatQuotientState_zero_right
      ν hν H).comp hShift

  have hEq :
      (fun y : ℝ =>
        h3RawFourierL2HeatQuotientState
          ν (y - t) hν H)
        =ᶠ[(𝓝[Set.Ioi t] t)]
      (slope
        (h3RawFourierL2HeatRealPath
          ν hν G)
        t) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    dsimp only [H]
    exact
      (h3RawFourierL2HeatRealPath_slope_eq_quotient
        hν ht hy G).symm

  dsimp only [H] at hConv

  exact
    Tendsto.congr'
      hEq
      hConv

end

end Euclidean
end Bridge
end PrimeTensor
