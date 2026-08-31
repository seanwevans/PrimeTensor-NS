import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.C1PointEvaluationBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityThirdJetContinuity

/-!
# Selected physical velocity: zero-order time continuity

The weighted H³ selected mild path is already continuous as a spectral state.
`C1PointEvaluationBound` supplies the missing quantitative decoder estimate.

This file first records linearity of the classical inverse-Fourier
representative under subtraction and upgrades the point-evaluation estimate to

    ‖u_F(x) - u_G(x)‖ ≤ C_dw ‖F - G‖.

Thus inverse-Fourier point evaluation is continuous in the H³ spectral norm.
Applying this coordinatewise to the globally continuous physical extension of
the selected mild path proves ordinary pointwise time continuity of every real
velocity component.

This closes the `C⁰` half of the selected temporal `C¹` frontier.  The
remaining temporal work is differentiability and continuity of the time
derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSelectedVelocityTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Difference form of the H³ point-evaluation estimate. -/
theorem norm_h3SpectralScalarC1Representative_sub_apply_le
    (F G : H3SpectralScalarState)
    (x : H3FourierPoint3) :
    ‖h3SpectralScalarC1Representative F x
        -
      h3SpectralScalarC1Representative G x‖
      ≤
    h3RawFourierL1DeweightingCoefficient * ‖F - G‖ := by
  rw [
    ← congrFun (h3SpectralScalarC1Representative_sub F G) x
  ]

  exact
    norm_h3SpectralScalarC1Representative_apply_le
      (F - G) x

/-- H³ spectral continuity implies pointwise continuity of the complex
classical inverse-Fourier representative. -/
theorem h3SpectralScalarC1Representative_continuousAt_of_spectral
    (F : ℝ → H3SpectralScalarState)
    (s : ℝ)
    (hF : ContinuousAt F s)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun r : ℝ =>
        h3SpectralScalarC1Representative (F r) x)
      s := by
  change
    Tendsto
      (fun r : ℝ =>
        h3SpectralScalarC1Representative (F r) x)
      (𝓝 s)
      (𝓝 (h3SpectralScalarC1Representative (F s) x))

  rw [tendsto_iff_norm_sub_tendsto_zero]

  have hDiffCont :
      ContinuousAt
        (fun r : ℝ => F r - F s)
        s :=
    hF.sub continuousAt_const

  have hNormCont :
      ContinuousAt
        (fun r : ℝ => ‖F r - F s‖)
        s :=
    hDiffCont.norm

  have hNormTendsto :
      Tendsto
        (fun r : ℝ => ‖F r - F s‖)
        (𝓝 s)
        (𝓝 0) := by
    change
      Tendsto
        (fun r : ℝ => ‖F r - F s‖)
        (𝓝 s)
        (𝓝 ‖F s - F s‖)
      at hNormCont
    simpa only [sub_self, norm_zero] using hNormCont

  have hUpperTendsto :
      Tendsto
        (fun r : ℝ =>
          h3RawFourierL1DeweightingCoefficient *
            ‖F r - F s‖)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hNormTendsto)

  apply squeeze_zero'
  · exact
      Filter.Eventually.of_forall
        (fun r =>
          norm_nonneg
            (h3SpectralScalarC1Representative (F r) x
              -
            h3SpectralScalarC1Representative (F s) x))
  · exact
      Filter.Eventually.of_forall
        (fun r =>
          norm_h3SpectralScalarC1Representative_sub_apply_le
            (F r) (F s) x)
  · exact hUpperTendsto

/-- The real `Point3` representative inherits pointwise time continuity from a
continuous scalar spectral path. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_continuousAt_of_spectral
    (F : ℝ → H3SpectralScalarState)
    (s : ℝ)
    (hF : ContinuousAt F s)
    (x : Point3) :
    ContinuousAt
      (fun r : ℝ =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (F r) x)
      s := by
  have hComplex :
      ContinuousAt
        (fun r : ℝ =>
          h3SpectralScalarC1Representative
            (F r)
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        s :=
    h3SpectralScalarC1Representative_continuousAt_of_spectral
      F s hF
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  unfold
    h3SpectralScalarRealC1RepresentativeOnPoint3
    h3SpectralScalarRealC1Representative

  exact
    Complex.reCLM.continuous.continuousAt.comp hComplex

/-- Every selected reconstructed real velocity component is continuous in
restart-relative time.  This is stronger than the open-window statement needed
for temporal classicalization: the zero-extended spectral mild path is already
continuous on all real times. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_continuous
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun s : ℝ =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hA hU₀ s x).component j) := by
  let R₀ : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)

  have hWcont : Continuous W := by
    simpa only [
      W,
      R₀,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.1

  have hCoordCont :
      Continuous
        (fun s : ℝ =>
          W s (h3ClassicalizationFinOfAxis j)) :=
    (continuous_apply (h3ClassicalizationFinOfAxis j)).comp hWcont

  rw [continuous_iff_continuousAt]
  intro s

  change
    ContinuousAt
      (fun r : ℝ =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (W r (h3ClassicalizationFinOfAxis j))
          x)
      s

  exact
    h3SpectralScalarRealC1RepresentativeOnPoint3_continuousAt_of_spectral
      (fun r : ℝ =>
        W r (h3ClassicalizationFinOfAxis j))
      s
      hCoordCont.continuousAt
      x

/-- Velocity-level zero-order time continuity on the whole selected path. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_timeContinuous
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    ∀
      (x : Point3)
      (j : PrimeTensor.Axis Depth.three),
        Continuous
          (fun s : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀ s x).component j) := by
  intro x j
  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_continuous
      hν U₀ hA hU₀ x j

end
end Euclidean
end Bridge
end PrimeTensor
