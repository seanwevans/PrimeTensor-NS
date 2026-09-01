import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.HistoryRepresentativeQuotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.FreshTailQuotient

/-!
# Selected Duhamel diagonal right-quotient candidate

The two analytic pieces of the diagonal time derivative are now independently
closed in the exact physical pointwise form:

* the old-history heat increment quotient tends to the zero-time heat
  generator of the complete selected Duhamel field;
* the fresh moving-endpoint quotient tends to the instantaneous unheated
  nonlinear forcing.

This file performs only the topological assembly of those two limits.

Thus, as `h ↓ 0`,

    h⁻¹ • (H_h D(t) - D(t))
      + h⁻¹ • ∫ₜ^{t+h} H_{t+h-s} F(W(s),W(s)) ds

converges to

    G_history(t) + F(W(t),W(t)).

A second theorem packages the same expression under one scalar action.  The
next checkpoint is then purely algebraic: the physical Duhamel cocycle must
identify that one-smul expression with

    h⁻¹ • (D(t+h) - D(t)).

No further dominated-convergence argument remains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3DuhamelDiagonalRightCandidate
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The separately normalized old-history and fresh-tail quotients converge
jointly to the sum of the history heat generator and instantaneous forcing. -/
theorem tendsto_h3SelectedDuhamelDiagonalRightCandidate_sum_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
            (h3SelectedDuhamelHistoryHeatRepresentative
                ν A t h hν U₀ hA hU₀ ht i x
              -
            h3SelectedDuhamelC1Representative
                ν A t hν U₀ hA hU₀ ht i x)
          +
        h⁻¹ •
            (∫ s in t..t + h,
              h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
                ν (t + h) W W i x s))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatTimeGeneratorRepresentative
            ν A t hν U₀ hA hU₀ ht i x
          +
        h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i x)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW :
      Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hHistory :=
    tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeatRepresentative_C1_zero_right
      hν U₀ hA hU₀ ht htR i x

  have hFresh :=
    tendsto_inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshTail_selectedRestart_zero_right
      (t := t)
      hν U₀ hA hU₀ hW i x

  dsimp only [W] at hHistory hFresh ⊢
  exact hHistory.add hFresh

/-- Equivalent one-smul form of the assembled diagonal right-quotient
candidate.  This is the form that the physical Duhamel cocycle will identify
with the actual diagonal difference quotient. -/
theorem tendsto_h3SelectedDuhamelDiagonalRightCandidate_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          ((h3SelectedDuhamelHistoryHeatRepresentative
                ν A t h hν U₀ hA hU₀ ht i x
              -
            h3SelectedDuhamelC1Representative
                ν A t hν U₀ hA hU₀ ht i x)
            +
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
              ν (t + h) W W i x s)))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatTimeGeneratorRepresentative
            ν A t hν U₀ hA hU₀ ht i x
          +
        h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i x)) := by
  have hSum :=
    tendsto_h3SelectedDuhamelDiagonalRightCandidate_sum_zero_right
      hν U₀ hA hU₀ ht htR i x

  simpa only [smul_add] using hSum

end

end Euclidean
end Bridge
end PrimeTensor
