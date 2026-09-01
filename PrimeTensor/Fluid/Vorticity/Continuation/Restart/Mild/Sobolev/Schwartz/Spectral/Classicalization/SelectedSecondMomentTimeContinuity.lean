import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedSecondMomentDifferenceContinuity

/-!
# Classicalization: selected second raw Fourier moment time continuity

`SelectedSecondMomentDifferenceContinuity` proves that at every strict positive
interior restart time `s`,

    m₂(W(r)_i - W(s)_i) → 0.

This file converts that difference statement into ordinary continuity of the
selected coordinate second raw Fourier mass itself.

The only extra ingredient is the reverse-triangle estimate

    |m₂(F) - m₂(G)| ≤ m₂(F - G),

valid whenever the three second moments are integrable.  It follows directly
from the almost-everywhere subtraction identity for the canonical raw Fourier
representative and the norm triangle inequality.

Consequently every selected coordinate satisfies

    r ↦ m₂(W(r)_i)

continuously on the strict positive interior restart interval.  This gives the
bounded nonvanishing state factor needed when the next layer estimates the
first Fourier moment of the nonlinear forcing difference.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSecondMomentTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Reverse-triangle control for the second raw Fourier mass. -/
theorem abs_h3SpectralScalarRawFourierSecondMass_sub_le
    (F G : H3SpectralScalarState)
    (hF2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3))
    (hG2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3))
    (hD2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3)) :
    |h3SpectralScalarRawFourierSecondMass F -
        h3SpectralScalarRawFourierSecondMass G|
      ≤
    h3SpectralScalarRawFourierSecondMass (F - G) := by
  have hSub0 :=
    h3SpectralScalarRawFourier_sub_ae F G

  have hSub :
      h3SpectralScalarRawFourier (F - G)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ) := by
    simpa only [
      axisFintypeH3SelectedSecondMomentTimeContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hSub0

  have hForwardPoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier F ξ‖
          ≤
        ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (F - G) ξ‖
          +
        ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier G ξ‖ := by
    filter_upwards [hSub] with ξ hξ

    have hw : 0 ≤ ‖ξ‖ ^ 2 :=
      pow_nonneg (norm_nonneg ξ) 2

    have hNorm :
        ‖h3SpectralScalarRawFourier F ξ‖
          ≤
        ‖h3SpectralScalarRawFourier (F - G) ξ‖ +
          ‖h3SpectralScalarRawFourier G ξ‖ := by
      rw [hξ]
      simpa only [sub_add_cancel] using
        norm_add_le
          (h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ)
          (h3SpectralScalarRawFourier G ξ)

    calc
      ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier F ξ‖
          ≤
        ‖ξ‖ ^ 2 *
          (‖h3SpectralScalarRawFourier (F - G) ξ‖ +
            ‖h3SpectralScalarRawFourier G ξ‖) :=
        mul_le_mul_of_nonneg_left hNorm hw
      _ =
        ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (F - G) ξ‖
          +
        ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier G ξ‖ := by
        ring

  have hForwardInt :
      h3SpectralScalarRawFourierSecondMass F
        ≤
      h3SpectralScalarRawFourierSecondMass (F - G) +
        h3SpectralScalarRawFourierSecondMass G := by
    have hMajor := hD2.add hG2
    have h :=
      integral_mono_ae hF2 hMajor hForwardPoint

    have hSum :
        (∫ ξ : H3FourierPoint3,
          ((fun η : H3FourierPoint3 =>
              ‖η‖ ^ 2 *
                ‖h3SpectralScalarRawFourier (F - G) η‖)
            +
            (fun η : H3FourierPoint3 =>
              ‖η‖ ^ 2 *
                ‖h3SpectralScalarRawFourier G η‖)) ξ)
          =
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier G ξ‖ := by
      simpa only [Pi.add_apply] using
        (integral_add hD2 hG2)

    unfold h3SpectralScalarRawFourierSecondMass
    exact h.trans_eq hSum

  have hReversePoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier G ξ‖
          ≤
        ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (F - G) ξ‖
          +
        ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier F ξ‖ := by
    filter_upwards [hSub] with ξ hξ

    have hw : 0 ≤ ‖ξ‖ ^ 2 :=
      pow_nonneg (norm_nonneg ξ) 2

    have hAlg :
        -(h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ)
          +
        h3SpectralScalarRawFourier F ξ
          =
        h3SpectralScalarRawFourier G ξ := by
      ring

    have hNorm :
        ‖h3SpectralScalarRawFourier G ξ‖
          ≤
        ‖h3SpectralScalarRawFourier (F - G) ξ‖ +
          ‖h3SpectralScalarRawFourier F ξ‖ := by
      rw [hξ]
      have h :=
        norm_add_le
          (-(h3SpectralScalarRawFourier F ξ -
              h3SpectralScalarRawFourier G ξ))
          (h3SpectralScalarRawFourier F ξ)
      rw [hAlg] at h
      simpa only [norm_neg] using h

    calc
      ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier G ξ‖
          ≤
        ‖ξ‖ ^ 2 *
          (‖h3SpectralScalarRawFourier (F - G) ξ‖ +
            ‖h3SpectralScalarRawFourier F ξ‖) :=
        mul_le_mul_of_nonneg_left hNorm hw
      _ =
        ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (F - G) ξ‖
          +
        ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier F ξ‖ := by
        ring

  have hReverseInt :
      h3SpectralScalarRawFourierSecondMass G
        ≤
      h3SpectralScalarRawFourierSecondMass (F - G) +
        h3SpectralScalarRawFourierSecondMass F := by
    have hMajor := hD2.add hF2
    have h :=
      integral_mono_ae hG2 hMajor hReversePoint

    have hSum :
        (∫ ξ : H3FourierPoint3,
          ((fun η : H3FourierPoint3 =>
              ‖η‖ ^ 2 *
                ‖h3SpectralScalarRawFourier (F - G) η‖)
            +
            (fun η : H3FourierPoint3 =>
              ‖η‖ ^ 2 *
                ‖h3SpectralScalarRawFourier F η‖)) ξ)
          =
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier F ξ‖ := by
      simpa only [Pi.add_apply] using
        (integral_add hD2 hF2)

    unfold h3SpectralScalarRawFourierSecondMass
    exact h.trans_eq hSum

  rw [abs_le]
  constructor <;> linarith

/-- The selected positive-time coordinate second raw Fourier mass is continuous
at every strict positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_secondMass_continuousAt_time
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
        h3SpectralScalarRawFourierSecondMass (W r i))
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let M : ℝ → ℝ :=
    fun r =>
      h3SpectralScalarRawFourierSecondMass (W r i)

  have hDiffTend :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierSecondMass
            (W r i - W s i))
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_secondDifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR i

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hBound :
      ∀ᶠ r in 𝓝 s,
        |M r - M s|
          ≤
        h3SpectralScalarRawFourierSecondMass
          (W r i - W s i) := by
    filter_upwards [hInterval] with r hr

    have hr2 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (W r i) ξ‖)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMoment_integrable
          hν U₀ hA hU₀ hr.1 hr.2.le i

    have hs2 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (W s i) ξ‖)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMoment_integrable
          hν U₀ hA hU₀ hs hsR.le i

    have hrThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hr.1 hr.2.le i

    have hsThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hs hsR.le i

    have hrThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_three_classicalization_cubicFrechet
      ] using hrThreeOrd

    have hsThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W s i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_three_classicalization_cubicFrechet
      ] using hsThreeOrd

    have hDiffThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_three_sub
        (W r i) (W s i) hrThree hsThree

    have hDiff2 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier
                (W r i - W s i) ξ‖)
          (volume : Measure H3FourierPoint3) :=
      h3SpectralScalarRawFourier_natMoment_integrable_le_three_of_cubic
        (W r i - W s i)
        hDiffThree
        2
        (by norm_num)

    dsimp only [M]

    exact
      abs_h3SpectralScalarRawFourierSecondMass_sub_le
        (W r i) (W s i) hr2 hs2 hDiff2

  have hDistTend :
      Tendsto
        (fun r : ℝ => dist (M r) (M s))
        (𝓝 s)
        (𝓝 0) := by
    apply squeeze_zero'
    · exact
        Filter.Eventually.of_forall
          (fun r => dist_nonneg)
    · filter_upwards [hBound] with r hr
      simpa only [Real.dist_eq] using hr
    · exact hDiffTend

  change
    Tendsto M (𝓝 s) (𝓝 (M s))

  exact
    tendsto_iff_dist_tendsto_zero.2 hDistTend

end

end Euclidean
end Bridge
end PrimeTensor
