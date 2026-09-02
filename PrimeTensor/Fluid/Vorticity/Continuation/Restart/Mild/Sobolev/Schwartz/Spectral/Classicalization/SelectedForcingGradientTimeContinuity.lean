import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedForcingInverseFourierGradientDifferenceBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedForcingC1SpatialRegularity

/-!
# Classicalization: time continuity of the selected forcing gradient

The selected nonlinear forcing difference now tends to zero in the first
weighted raw Fourier `L¹` topology, and the inverse-Fourier derivative has a
uniform quantitative bound by exactly that topology.

This file combines those two facts.  At every fixed Fourier-side physical
point `x`, the Fréchet derivative

    D_x N(W(t), W(t))(x)

of the ordinary inverse-Fourier forcing representative is continuous in time
at every strict positive interior restart time.

No new nonlinear estimate is introduced.  The only local work is verifying
first-moment integrability of the two endpoint forcing amplitudes and of their
difference so the generic inverse-Fourier gradient bound can be applied.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingGradientTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Along the selected restart path, the spatial Fréchet derivative of the
instantaneous inverse-Fourier forcing representative is time-continuous at each
fixed Fourier Euclidean point. -/
theorem h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_fderiv_continuousAt_time
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
        fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W r) (W r) i)
          x)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : ℝ →
      (H3FourierPoint3 →L[ℝ] ℂ) :=
    fun r =>
      fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W r) (W r) i)
        x

  let M : ℝ → ℝ :=
    fun r =>
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence
              (W r) (W r) i ξ -
            h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ‖

  have hMassTend :
      Tendsto M
        (𝓝 s)
        (𝓝 0) := by
    have h :=
      h3RawFinLerayOuterProductDivergence_selectedRestart_differenceFirstMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR i
    simpa only [M, W] using h

  have hCoeffTend :
      Tendsto
        (fun _ : ℝ =>
          h3FourierFirstDerivativeL1Coefficient)
        (𝓝 s)
        (𝓝 h3FourierFirstDerivativeL1Coefficient) :=
    tendsto_const_nhds

  have hUpperTend :
      Tendsto
        (fun r : ℝ =>
          h3FourierFirstDerivativeL1Coefficient * M r)
        (𝓝 s)
        (𝓝 0) := by
    have h :=
      hCoeffTend.mul hMassTend
    simpa only [mul_zero] using h

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hBound :
      ∀ᶠ r in 𝓝 s,
        ‖F r - F s‖
          ≤
        h3FourierFirstDerivativeL1Coefficient * M r := by
    filter_upwards [hInterval] with r hr

    let fr : H3FourierPoint3 → ℂ :=
      h3RawFinLerayOuterProductDivergence
        (W r) (W r) i

    let fs : H3FourierPoint3 → ℂ :=
      h3RawFinLerayOuterProductDivergence
        (W s) (W s) i

    have hfr0 :
        Integrable fr
          (volume : Measure H3FourierPoint3) := by
      dsimp only [fr]
      exact
        h3RawFinLerayOuterProductDivergence_integrable
          (W r) (W r) i

    have hfs0 :
        Integrable fs
          (volume : Measure H3FourierPoint3) := by
      dsimp only [fs]
      exact
        h3RawFinLerayOuterProductDivergence_integrable
          (W s) (W s) i

    have hfr1 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ * ‖fr ξ‖)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [fr, W]
      exact
        h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
          hν U₀ hA hU₀ hr.1 hr.2.le i

    have hfs1 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ * ‖fs ξ‖)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [fs, W]
      exact
        h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
          hν U₀ hA hU₀ hs hsR.le i

    have hMajor :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ * ‖fr ξ‖ +
              ‖ξ‖ * ‖fs ξ‖)
          (volume : Measure H3FourierPoint3) :=
      hfr1.add hfs1

    have hDiff0 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            fr ξ - fs ξ)
          (volume : Measure H3FourierPoint3) :=
      hfr0.sub hfs0

    have hTargetMeas :
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ * ‖fr ξ - fs ξ‖)
          (volume : Measure H3FourierPoint3) :=
      continuous_norm.aestronglyMeasurable.mul
        hDiff0.aestronglyMeasurable.norm

    have hPoint :
        ∀ ξ : H3FourierPoint3,
          ‖ξ‖ * ‖fr ξ - fs ξ‖
            ≤
          ‖ξ‖ * ‖fr ξ‖ +
            ‖ξ‖ * ‖fs ξ‖ := by
      intro ξ
      calc
        ‖ξ‖ * ‖fr ξ - fs ξ‖
            ≤
          ‖ξ‖ * (‖fr ξ‖ + ‖fs ξ‖) :=
          mul_le_mul_of_nonneg_left
            (norm_sub_le (fr ξ) (fs ξ))
            (norm_nonneg ξ)
        _ =
          ‖ξ‖ * ‖fr ξ‖ +
            ‖ξ‖ * ‖fs ξ‖ := by
          ring

    have hDiff1 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ * ‖fr ξ - fs ξ‖)
          (volume : Measure H3FourierPoint3) := by
      refine hMajor.mono' hTargetMeas ?_
      filter_upwards with ξ
      have hLeft0 :
          0 ≤ ‖ξ‖ * ‖fr ξ - fs ξ‖ := by
        positivity
      have hRight0 :
          0 ≤
            ‖ξ‖ * ‖fr ξ‖ +
              ‖ξ‖ * ‖fs ξ‖ := by
        positivity
      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeft0,
        abs_of_nonneg hRight0
      ] using hPoint ξ

    have hBase :=
      norm_fderiv_fourierInv_sub_le_firstMass
        fr fs
        hfr0 hfs0
        hfr1 hfs1
        hDiff1
        x

    dsimp only [F, M]
    unfold
      h3RawFinLerayOuterProductDivergenceC0Representative

    simpa only [fr, fs] using hBase

  have hNonneg :
      ∀ᶠ r in 𝓝 s,
        0 ≤ ‖F r - F s‖ :=
    Filter.Eventually.of_forall
      (fun r => norm_nonneg (F r - F s))

  have hNormTend :
      Tendsto
        (fun r : ℝ => ‖F r - F s‖)
        (𝓝 s)
        (𝓝 0) :=
    squeeze_zero'
      hNonneg
      hBound
      hUpperTend

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
