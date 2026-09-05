import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Second.Moment.Time.Continuity

/-!
# Classicalization: selected raw Fourier L1 mass time continuity

The weighted first-moment forcing difference bound contains both zeroth and
second raw Fourier masses of the selected state.

`SelectedSecondMomentTimeContinuity` already supplies continuity of the second
mass.  This file records the matching zeroth-mass statement.

For scalar spectral states,

    |m0(F) - m0(G)| ≤ m0(F - G),

by the almost-everywhere subtraction identity and the reverse triangle
inequality for norms.  Along the selected H3-continuous restart path,

    m0(W(r)_i - W(s)_i)
      ≤ C_deweight ‖W(r)_i - W(s)_i‖ → 0.

Hence the raw Fourier L1 mass of every selected coordinate is continuous at
every strict positive interior restart time.

No new PDE estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedL1MassTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Reverse-triangle control for the raw Fourier `L1` mass. -/
theorem abs_h3SpectralScalarRawFourierL1Mass_sub_le
    (F G : H3SpectralScalarState) :
    |h3SpectralScalarRawFourierL1Mass F -
        h3SpectralScalarRawFourierL1Mass G|
      ≤
    h3SpectralScalarRawFourierL1Mass (F - G) := by
  have hF0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 F)

  have hG0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hD0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 (F - G))

  have hF :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3SelectedL1MassTimeContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hF0.norm

  have hG :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3SelectedL1MassTimeContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hG0.norm

  have hD :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3SelectedL1MassTimeContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hD0.norm

  have hSub0 :=
    h3SpectralScalarRawFourier_sub_ae F G

  have hSub :
      h3SpectralScalarRawFourier (F - G)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ) := by
    simpa only [
      axisFintypeH3SelectedL1MassTimeContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hSub0

  have hForwardPoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖h3SpectralScalarRawFourier F ξ‖
          ≤
        ‖h3SpectralScalarRawFourier (F - G) ξ‖ +
          ‖h3SpectralScalarRawFourier G ξ‖ := by
    filter_upwards [hSub] with ξ hξ
    rw [hξ]
    simpa only [sub_add_cancel] using
      norm_add_le
        (h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ)
        (h3SpectralScalarRawFourier G ξ)

  have hForwardInt :
      h3SpectralScalarRawFourierL1Mass F
        ≤
      h3SpectralScalarRawFourierL1Mass (F - G) +
        h3SpectralScalarRawFourierL1Mass G := by
    have hMajor := hD.add hG
    have h :=
      integral_mono_ae hF hMajor hForwardPoint

    have hSum :
        (∫ ξ : H3FourierPoint3,
          ((fun η : H3FourierPoint3 =>
              ‖h3SpectralScalarRawFourier (F - G) η‖)
            +
            (fun η : H3FourierPoint3 =>
              ‖h3SpectralScalarRawFourier G η‖)) ξ)
          =
        (∫ ξ : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        ∫ ξ : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier G ξ‖ := by
      simpa only [Pi.add_apply] using
        (integral_add hD hG)

    unfold h3SpectralScalarRawFourierL1Mass
    exact h.trans_eq hSum

  have hReversePoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖h3SpectralScalarRawFourier G ξ‖
          ≤
        ‖h3SpectralScalarRawFourier (F - G) ξ‖ +
          ‖h3SpectralScalarRawFourier F ξ‖ := by
    filter_upwards [hSub] with ξ hξ

    have hAlg :
        -(h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ)
          +
        h3SpectralScalarRawFourier F ξ
          =
        h3SpectralScalarRawFourier G ξ := by
      ring

    rw [hξ]
    have h :=
      norm_add_le
        (-(h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ))
        (h3SpectralScalarRawFourier F ξ)
    rw [hAlg] at h
    simpa only [norm_neg] using h

  have hReverseInt :
      h3SpectralScalarRawFourierL1Mass G
        ≤
      h3SpectralScalarRawFourierL1Mass (F - G) +
        h3SpectralScalarRawFourierL1Mass F := by
    have hMajor := hD.add hF
    have h :=
      integral_mono_ae hG hMajor hReversePoint

    have hSum :
        (∫ ξ : H3FourierPoint3,
          ((fun η : H3FourierPoint3 =>
              ‖h3SpectralScalarRawFourier (F - G) η‖)
            +
            (fun η : H3FourierPoint3 =>
              ‖h3SpectralScalarRawFourier F η‖)) ξ)
          =
        (∫ ξ : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        ∫ ξ : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F ξ‖ := by
      simpa only [Pi.add_apply] using
        (integral_add hD hF)

    unfold h3SpectralScalarRawFourierL1Mass
    exact h.trans_eq hSum

  rw [abs_le]
  constructor <;> linarith

/-- The raw Fourier `L1` mass of each selected coordinate is time-continuous at
every strict positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        h3SpectralScalarRawFourierL1Mass (W r i))
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : ℝ → H3SpectralScalarState :=
    fun r => W r i

  let M : ℝ → ℝ :=
    fun r =>
      h3SpectralScalarRawFourierL1Mass (F r)

  have hWContinuous : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hFContinuous : Continuous F := by
    dsimp only [F]
    exact
      (continuous_apply i).comp hWContinuous

  have hNormTend :
      Tendsto
        (fun r : ℝ => ‖F r - F s‖)
        (𝓝 s)
        (𝓝 0) := by
    have hAt :
        ContinuousAt
          (fun r : ℝ => ‖F r - F s‖)
          s :=
      (hFContinuous.continuousAt.sub continuousAt_const).norm

    change
      Tendsto
        (fun r : ℝ => ‖F r - F s‖)
        (𝓝 s)
        (𝓝 ‖F s - F s‖)
      at hAt

    simpa only [sub_self, norm_zero] using hAt

  have hUpperTend :
      Tendsto
        (fun r : ℝ =>
          h3RawFourierL1DeweightingCoefficient *
            ‖F r - F s‖)
        (𝓝 s)
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _ : ℝ => h3RawFourierL1DeweightingCoefficient)
          (𝓝 s)
          (𝓝 h3RawFourierL1DeweightingCoefficient) :=
      tendsto_const_nhds

    have hMul :=
      hConst.mul hNormTend

    simpa only [mul_zero] using hMul

  have hDiffTend :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierL1Mass
            (F r - F s))
        (𝓝 s)
        (𝓝 0) := by
    apply squeeze_zero
    · intro r
      exact
        h3SpectralScalarRawFourierL1Mass_nonneg
          (F r - F s)
    · intro r
      exact
        h3SpectralScalarRawFourierL1Mass_le_norm
          (F r - F s)
    · exact hUpperTend

  have hBound :
      ∀ r : ℝ,
        |M r - M s|
          ≤
        h3SpectralScalarRawFourierL1Mass
          (F r - F s) := by
    intro r
    dsimp only [M]
    exact
      abs_h3SpectralScalarRawFourierL1Mass_sub_le
        (F r) (F s)

  have hDistTend :
      Tendsto
        (fun r : ℝ => dist (M r) (M s))
        (𝓝 s)
        (𝓝 0) := by
    apply squeeze_zero
    · intro r
      exact dist_nonneg
    · intro r
      simpa only [Real.dist_eq] using hBound r
    · exact hDiffTend

  change
    Tendsto M (𝓝 s) (𝓝 (M s))

  exact
    tendsto_iff_dist_tendsto_zero.2 hDistTend

end

end Euclidean
end Bridge
end PrimeTensor
