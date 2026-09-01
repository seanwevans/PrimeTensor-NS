import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.CubicFrechetContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.SecondMildMass

/-!
# Classicalization: selected second-moment difference continuity

The first spatial derivative of the instantaneous nonlinear forcing is governed
by one weighted Fourier moment of the forcing.  The bilinear first-moment
forcing estimate in turn spends the second raw Fourier moments of its state
inputs.

For a selected positive-time path we do not need, and must not assume, a
generic H³-to-second-raw-`L¹` estimate.  Instead the already-closed cubic
weighted-Fourier continuity gives the correct topology bridge.

Pointwise,

    |ξ|² ≤ 1 + |ξ|³,

hence for every scalar spectral state carrying a cubic raw Fourier moment,

    m₂(H) ≤ m₀(H) + m₃(H).

Apply this to the difference

    H = W(r)_i - W(s)_i.

The unweighted mass tends to zero by H³ continuity and the existing
deweighting bound, while `CubicTimeContinuity` already proves that the cubic
difference mass tends to zero.  Therefore the second raw Fourier mass of the
selected state difference also tends to zero at every strict positive interior
restart time.

This is the quantitative input needed by the next forcing-gradient continuity
layer.  No new Navier--Stokes or heat-kernel estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSecondMomentDifferenceContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- A cubic raw Fourier moment controls the second raw Fourier mass up to the
ambient unweighted raw `L¹` mass. -/
theorem h3SpectralScalarRawFourierSecondMass_le_l1_add_thirdMass
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H) :
    h3SpectralScalarRawFourierSecondMass H
      ≤
    h3SpectralScalarRawFourierL1Mass H +
      h3SpectralScalarRawFourierMomentMass (3 : ℝ) H := by
  have hTwo :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourier_natMoment_integrable_le_three_of_cubic
      H hThree 2 (by norm_num)

  have hZero0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 H)

  have hZero :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3SelectedSecondMomentDifferenceContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hZero0.norm

  have hThree' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hThree
    refine hThree.congr ?_
    filter_upwards with ξ
    rw [h3FourierMomentWeight_three_classicalization_cubicFrechet ξ]

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier H ξ‖ +
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hZero.add hThree'

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier H ξ‖
          ≤
        ‖h3SpectralScalarRawFourier H ξ‖ +
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier H ξ‖ := by
    intro ξ

    have hx0 : 0 ≤ ‖ξ‖ :=
      norm_nonneg ξ

    have hPow :
        ‖ξ‖ ^ 2 ≤ 1 + ‖ξ‖ ^ 3 := by
      by_cases hx : ‖ξ‖ ≤ 1
      · have h20 : 0 ≤ ‖ξ‖ ^ 2 :=
          pow_nonneg hx0 2
        have h21 : ‖ξ‖ ^ 2 ≤ 1 := by
          nlinarith
        have h30 : 0 ≤ ‖ξ‖ ^ 3 :=
          pow_nonneg hx0 3
        linarith
      · have hx1 : 1 ≤ ‖ξ‖ :=
          le_of_lt (lt_of_not_ge hx)
        have h20 : 0 ≤ ‖ξ‖ ^ 2 :=
          pow_nonneg hx0 2
        have h23 :
            ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 3 := by
          calc
            ‖ξ‖ ^ 2 = ‖ξ‖ ^ 2 * 1 := by ring
            _ ≤ ‖ξ‖ ^ 2 * ‖ξ‖ :=
              mul_le_mul_of_nonneg_left hx1 h20
            _ = ‖ξ‖ ^ 3 := by ring
        linarith

    have hNorm0 :
        0 ≤ ‖h3SpectralScalarRawFourier H ξ‖ :=
      norm_nonneg _

    calc
      ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier H ξ‖
          ≤
        (1 + ‖ξ‖ ^ 3) *
          ‖h3SpectralScalarRawFourier H ξ‖ :=
        mul_le_mul_of_nonneg_right hPow hNorm0
      _ =
        ‖h3SpectralScalarRawFourier H ξ‖ +
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier H ξ‖ := by
        ring

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier H ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖h3SpectralScalarRawFourier H ξ‖ +
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier H ξ‖) := by
    exact
      integral_mono_ae
        hTwo
        hMajor
        (Filter.Eventually.of_forall hPoint)

  have hThirdMassEq :
      h3SpectralScalarRawFourierMomentMass (3 : ℝ) H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [h3FourierMomentWeight_three_classicalization_cubicFrechet ξ]

  calc
    h3SpectralScalarRawFourierSecondMass H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
      rfl
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (‖h3SpectralScalarRawFourier H ξ‖ +
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier H ξ‖) :=
      hIntegral
    _ =
      (∫ ξ : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier H ξ‖)
        +
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
      rw [integral_add hZero hThree']
    _ =
      h3SpectralScalarRawFourierL1Mass H +
        h3SpectralScalarRawFourierMomentMass (3 : ℝ) H := by
      rw [hThirdMassEq]
      rfl

/-- At every strict positive interior restart time, the second raw Fourier
mass of each selected coordinate difference tends to zero. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_secondDifferenceMass_tendsto_zero
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
    Tendsto
      (fun r : ℝ =>
        h3SpectralScalarRawFourierSecondMass
          (W r i - W s i))
      (𝓝 s)
      (𝓝 0) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : ℝ → H3SpectralScalarState :=
    fun r => W r i

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

  have hL1UpperTend :
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

  have hL1Tend :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierL1Mass
            (F r - F s))
        (𝓝 s)
        (𝓝 0) := by
    apply squeeze_zero
    · intro r
      unfold h3SpectralScalarRawFourierL1Mass
      exact integral_nonneg (fun ξ => norm_nonneg _)
    · intro r
      exact
        h3SpectralScalarRawFourierL1Mass_le_norm
          (F r - F s)
    · exact hL1UpperTend

  have hThirdTend :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierMomentMass
            (3 : ℝ)
            (F r - F s))
        (𝓝 s)
        (𝓝 0) := by
    dsimp only [F, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_cubicDifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR i

  have hUpperTend :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierL1Mass
              (F r - F s)
            +
          h3SpectralScalarRawFourierMomentMass
              (3 : ℝ)
              (F r - F s))
        (𝓝 s)
        (𝓝 0) := by
    simpa only [zero_add] using
      hL1Tend.add hThirdTend

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hSecondUpper :
      ∀ᶠ r in 𝓝 s,
        h3SpectralScalarRawFourierSecondMass
            (F r - F s)
          ≤
        h3SpectralScalarRawFourierL1Mass
            (F r - F s)
          +
        h3SpectralScalarRawFourierMomentMass
            (3 : ℝ)
            (F r - F s) := by
    filter_upwards [hInterval] with r hr

    have hrThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hr.1 hr.2.le i

    have hsThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hs hsR.le i

    have hrThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (F r) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        F, W,
        h3FourierMomentWeight_three_classicalization_cubicFrechet
      ] using hrThreeOrd

    have hsThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (F s) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        F, W,
        h3FourierMomentWeight_three_classicalization_cubicFrechet
      ] using hsThreeOrd

    have hDiffThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (F r - F s) :=
      h3RawFourierMomentIntegrable_three_sub
        (F r) (F s) hrThree hsThree

    exact
      h3SpectralScalarRawFourierSecondMass_le_l1_add_thirdMass
        (F r - F s) hDiffThree

  have hSecondNonneg :
      ∀ᶠ r in 𝓝 s,
        0 ≤
          h3SpectralScalarRawFourierSecondMass
            (F r - F s) :=
    Filter.Eventually.of_forall
      (fun r =>
        h3SpectralScalarRawFourierSecondMass_nonneg
          (F r - F s))

  have hTarget :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierSecondMass
            (F r - F s))
        (𝓝 s)
        (𝓝 0) :=
    squeeze_zero'
      hSecondNonneg
      hSecondUpper
      hUpperTend

  simpa only [F, W] using hTarget

end

end Euclidean
end Bridge
end PrimeTensor
