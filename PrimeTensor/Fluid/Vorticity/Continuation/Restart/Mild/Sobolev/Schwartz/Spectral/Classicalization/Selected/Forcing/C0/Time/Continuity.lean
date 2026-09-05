import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Hessian.Trace.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.C0.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Forcing.HalfHolder

/-!
# Classicalization: time continuity of the instantaneous C0 nonlinear forcing

The selected classical Duhamel right derivative has two summands:

    ν * trace(D² Duhamel(t))
      +
    N(W(t), W(t))(x).

`SelectedDuhamelHessianTraceTimeContinuity` closes continuity of the first
summand.  This file closes the second.

The endpoint forcing branch already proves the quantitative diagonal raw
Fourier `L¹` difference estimate

    ∫ ‖N̂(U,U) - N̂(V,V)‖
      ≤
    C ‖U-V‖ ‖U‖ + C ‖V‖ ‖U-V‖.

The ordinary inverse Fourier transform has point-evaluation norm at most its
raw `L¹` mass.  Consequently, at every fixed spatial point,

    ‖N_C0(U,U)(x) - N_C0(V,V)(x)‖
      ≤
    C ‖U-V‖ ‖U‖ + C ‖V‖ ‖U-V‖.

Composing this estimate with continuity of the Banach-selected restart path
gives time continuity of the instantaneous physical forcing at every strict
positive interior restart time.

No new nonlinear estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedForcingC0TimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fixed-point inverse-Fourier stability of the diagonal unheated nonlinear
forcing.  The physical C0 difference is bounded by the already-closed raw
Fourier L1 state-difference estimate. -/
theorem norm_h3RawFinLerayOuterProductDivergenceC0Representative_diagonal_sub_le_stateDifference
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceC0Representative
          U U i x
        -
      h3RawFinLerayOuterProductDivergenceC0Representative
          V V i x‖
      ≤
    h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
      h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖ := by
  let FU : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence U U i

  let FV : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence V V i

  have hFU :
      Integrable FU
        (volume : Measure H3FourierPoint3) := by
    dsimp only [FU]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        U U i

  have hFV :
      Integrable FV
        (volume : Measure H3FourierPoint3) := by
    dsimp only [FV]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        V V i

  have hInnerContinuous :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          inner ℝ ξ x) := by
    fun_prop

  have hPhaseContinuous :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          Real.fourierChar (inner ℝ ξ x)) :=
    Real.continuous_fourierChar.comp hInnerContinuous

  have hFUPhaseMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          Real.fourierChar (inner ℝ ξ x) • FU ξ)
        (volume : Measure H3FourierPoint3) :=
    hPhaseContinuous.aestronglyMeasurable.fun_smul hFU.1

  have hFUPhase :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          Real.fourierChar (inner ℝ ξ x) • FU ξ)
        (volume : Measure H3FourierPoint3) := by
    rw [← integrable_norm_iff hFUPhaseMeas]
    simpa only [Circle.norm_smul] using hFU.norm

  have hFVPhaseMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          Real.fourierChar (inner ℝ ξ x) • FV ξ)
        (volume : Measure H3FourierPoint3) :=
    hPhaseContinuous.aestronglyMeasurable.fun_smul hFV.1

  have hFVPhase :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          Real.fourierChar (inner ℝ ξ x) • FV ξ)
        (volume : Measure H3FourierPoint3) := by
    rw [← integrable_norm_iff hFVPhaseMeas]
    simpa only [Circle.norm_smul] using hFV.norm

  unfold
    h3RawFinLerayOuterProductDivergenceC0Representative

  rw [
    Real.fourierInv_eq,
    Real.fourierInv_eq,
    ← integral_sub hFUPhase hFVPhase
  ]

  calc
    ‖∫ ξ : H3FourierPoint3,
        Real.fourierChar (inner ℝ ξ x) • FU ξ -
          Real.fourierChar (inner ℝ ξ x) • FV ξ‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖Real.fourierChar (inner ℝ ξ x) • FU ξ -
          Real.fourierChar (inner ℝ ξ x) • FV ξ‖ :=
      norm_integral_le_integral_norm _
    _ =
      ∫ ξ : H3FourierPoint3,
        ‖FU ξ - FV ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [← smul_sub, Circle.norm_smul]
    _ ≤
      h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
        h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖ := by
      dsimp only [FU, FV]
      exact
        h3RawFinLerayOuterProductDivergence_diagonal_differenceL1Mass_le
          U V i

/-- Along the Banach-selected restart path, the instantaneous unheated physical
forcing is time-continuous at every strict positive interior restart time. -/
theorem h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_diagonal_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceC0Representative
          (W r) (W r) i x)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let C : ℝ :=
    h3NonlinearForcingL1Coefficient

  let d : ℝ → ℝ :=
    fun r => ‖W r - W s‖

  let n : ℝ → ℝ :=
    fun r => ‖W r‖

  let R : ℝ → ℝ :=
    fun r =>
      C * d r * n r +
        C * ‖W s‖ * d r

  let F : ℝ → ℂ :=
    fun r =>
      h3RawFinLerayOuterProductDivergenceC0Representative
        (W r) (W r) i x

  have hWContinuous : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWAt : ContinuousAt W s :=
    hWContinuous.continuousAt

  have hdAt :
      ContinuousAt d s := by
    dsimp only [d]
    exact
      (hWAt.sub continuousAt_const).norm

  have hnAt :
      ContinuousAt n s := by
    dsimp only [n]
    exact hWAt.norm

  have hRAt :
      ContinuousAt R s := by
    dsimp only [R]
    exact
      (((continuousAt_const.mul hdAt).mul hnAt).add
        (continuousAt_const.mul hdAt))

  have hRs : R s = 0 := by
    simp [R, d]

  have hRtend :
      Tendsto
        R
        (𝓝 s)
        (𝓝 0) := by
    change
      Tendsto
        R
        (𝓝 s)
        (𝓝 (R s))
      at hRAt
    rw [hRs] at hRAt
    exact hRAt

  have hBound :
      ∀ r : ℝ,
        ‖F r - F s‖ ≤ R r := by
    intro r
    dsimp only [F, R, C, d, n]
    exact
      norm_h3RawFinLerayOuterProductDivergenceC0Representative_diagonal_sub_le_stateDifference
        (W r) (W s) i x

  have hNormTend :
      Tendsto
        (fun r : ℝ => ‖F r - F s‖)
        (𝓝 s)
        (𝓝 0) := by
    exact
      squeeze_zero
        (fun r => norm_nonneg (F r - F s))
        hBound
        hRtend

  change
    Tendsto
      F
      (𝓝 s)
      (𝓝 (F s))

  exact
    tendsto_iff_norm_sub_tendsto_zero.2 hNormTend

end

end Euclidean
end Bridge
end PrimeTensor
