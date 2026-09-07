import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2HeatGeneratorConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Physical L² temporal admissibility: heat-generator derivative at zero

The preceding endpoint layer proves strong raw-Fourier-`L²` convergence of the
positive heat difference quotient to the quotient-safe generator

    ν • Δ̂_L² G.

This file packages that convergence as the actual one-sided Banach-space
derivative of the raw Fourier heat orbit at elapsed time zero.

The real-time wrapper uses `Real.toNNReal`; consequently the theorem is stated
as a derivative within `Ioi 0`.  No derivative across negative elapsed time is
asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatGeneratorDerivativeAtZero
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real-time raw Fourier heat orbit obtained by clamping elapsed time to the
nonnegative half-line. -/
noncomputable def h3RawFourierL2HeatRealPath
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (G : H3SpectralScalarState)
    (s : ℝ) :
    H3FourierComplexL2 :=
  h3HeatFrequencyApplyNN
    ν hν (Real.toNNReal s)
    (h3SpectralScalarRawFourierL2 G)

/-- The clamped raw Fourier heat orbit starts exactly from the deweighted
Fourier state. -/
@[simp]
theorem h3RawFourierL2HeatRealPath_zero
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (G : H3SpectralScalarState) :
    h3RawFourierL2HeatRealPath
        ν hν G 0
      =
    h3SpectralScalarRawFourierL2 G := by
  unfold h3RawFourierL2HeatRealPath

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3HeatFrequencyApplyNN_coeFn
      ν hν (Real.toNNReal (0 : ℝ))
      (h3SpectralScalarRawFourierL2 G)
  ] with ξ hξ

  rw [hξ]
  simp [h3HeatFourierSymbol]

/-- The packaged heat quotient is literally the slope of the real-time raw
Fourier heat orbit based at zero. -/
theorem h3RawFourierL2HeatQuotientState_eq_slope
    (ν h : ℝ)
    (hν : 0 ≤ ν)
    (G : H3SpectralScalarState) :
    h3RawFourierL2HeatQuotientState
        ν h hν G
      =
    slope
      (h3RawFourierL2HeatRealPath
        ν hν G)
      0 h := by
  rw [slope_def_module]
  rw [sub_zero]
  rw [h3RawFourierL2HeatRealPath_zero]
  rfl

/-- The raw Fourier heat orbit has the quotient-safe generator as its
right derivative at elapsed time zero. -/
theorem h3RawFourierL2HeatRealPath_hasDerivWithinAt_zero_right
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (G : H3SpectralScalarState) :
    HasDerivWithinAt
      (h3RawFourierL2HeatRealPath
        ν hν G)
      (h3RawFourierL2HeatGeneratorState
        ν G)
      (Set.Ioi (0 : ℝ))
      0 := by
  refine
    (hasDerivWithinAt_iff_tendsto_slope'
      (f := h3RawFourierL2HeatRealPath ν hν G)
      (f' := h3RawFourierL2HeatGeneratorState ν G)
      (s := Set.Ioi (0 : ℝ))
      (x := (0 : ℝ))
      (by simp)).2 ?_

  have hConv :=
    tendsto_h3RawFourierL2HeatQuotientState_zero_right
      ν hν G

  have hEq :
      (fun h : ℝ =>
        h3RawFourierL2HeatQuotientState
          ν h hν G)
        =ᶠ[(𝓝[Set.Ioi (0 : ℝ)] 0)]
      (slope
        (h3RawFourierL2HeatRealPath
          ν hν G)
        0) := by
    filter_upwards with h
    exact
      h3RawFourierL2HeatQuotientState_eq_slope
        ν h hν G

  exact
    Tendsto.congr'
      hEq
      hConv

end

end Euclidean
end Bridge
end PrimeTensor
