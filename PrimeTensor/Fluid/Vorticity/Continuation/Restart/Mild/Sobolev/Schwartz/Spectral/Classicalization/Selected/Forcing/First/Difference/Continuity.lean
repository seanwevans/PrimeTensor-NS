import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.L1.Mass.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.First.Difference.Bound

/-!
# Classicalization: selected forcing first-moment time continuity

The preceding layers now provide exactly the four scalar ingredients appearing
in the quantitative first-moment nonlinear difference estimate:

* zeroth raw Fourier mass of the selected state is continuous in time;
* second raw Fourier mass of the selected state is continuous in time;
* zeroth raw Fourier mass of the selected state difference tends to zero;
* second raw Fourier mass of the selected state difference tends to zero.

For the selected restart path `W`, the bilinear first-moment estimate therefore
forces

    ∫ |ξ| |N(W(r),W(r)) - N(W(s),W(s))| dξ → 0

at every strict positive interior restart time.

This is the Fourier topology needed to transport one spatial derivative of the
instantaneous forcing continuously in time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingFirstDifferenceContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Along the selected restart path, the raw Fourier `L¹` mass of a coordinate
difference tends to zero at every strict positive interior time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1DifferenceMass_tendsto_zero
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
        h3SpectralScalarRawFourierL1Mass
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

  apply squeeze_zero
  · intro r
    exact
      h3SpectralScalarRawFourierL1Mass_nonneg
        (F r - F s)
  · intro r
    exact
      h3SpectralScalarRawFourierL1Mass_le_norm
        (F r - F s)
  · simpa only [F, W] using hUpperTend

/-- The first weighted raw Fourier mass of the selected nonlinear forcing
difference tends to zero at every strict positive interior restart time. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_differenceFirstMass_tendsto_zero
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
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)
      (𝓝 s)
      (𝓝 0) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let leftTerm : ℝ → Fin 3 → Fin 3 → ℝ :=
    fun r k j =>
      (2 * Real.pi) *
        (2 *
          (h3SpectralScalarRawFourierSecondMass
                ((W r - W s) k) *
              h3SpectralScalarRawFourierL1Mass
                (W r j)
            +
            h3SpectralScalarRawFourierL1Mass
                ((W r - W s) k) *
              h3SpectralScalarRawFourierSecondMass
                (W r j)))

  let rightTerm : ℝ → Fin 3 → Fin 3 → ℝ :=
    fun r k j =>
      (2 * Real.pi) *
        (2 *
          (h3SpectralScalarRawFourierSecondMass
                (W s k) *
              h3SpectralScalarRawFourierL1Mass
                ((W r - W s) j)
            +
            h3SpectralScalarRawFourierL1Mass
                (W s k) *
              h3SpectralScalarRawFourierSecondMass
                ((W r - W s) j)))

  let Q : ℝ → ℝ :=
    fun r =>
      2 * (∑ k : Fin 3, ∑ j : Fin 3, leftTerm r k j)
        +
      2 * (∑ k : Fin 3, ∑ j : Fin 3, rightTerm r k j)

  have hD0 :
      ∀ k : Fin 3,
        Tendsto
          (fun r : ℝ =>
            h3SpectralScalarRawFourierL1Mass
              ((W r - W s) k))
          (𝓝 s)
          (𝓝 0) := by
    intro k
    have h :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1DifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR k
    change
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierL1Mass
            (W r k - W s k))
        (𝓝 s)
        (𝓝 0)
    simpa only [W] using h

  have hD2 :
      ∀ k : Fin 3,
        Tendsto
          (fun r : ℝ =>
            h3SpectralScalarRawFourierSecondMass
              ((W r - W s) k))
          (𝓝 s)
          (𝓝 0) := by
    intro k
    have h :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_secondDifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR k
    change
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierSecondMass
            (W r k - W s k))
        (𝓝 s)
        (𝓝 0)
    simpa only [W] using h

  have hU0 :
      ∀ j : Fin 3,
        Tendsto
          (fun r : ℝ =>
            h3SpectralScalarRawFourierL1Mass
              (W r j))
          (𝓝 s)
          (𝓝
            (h3SpectralScalarRawFourierL1Mass
              (W s j))) := by
    intro j
    have h :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_continuousAt_time
        hν U₀ hA hU₀ hs hsR j
    change
      ContinuousAt
        (fun r : ℝ =>
          h3SpectralScalarRawFourierL1Mass
            (W r j))
        s
    simpa only [W] using h

  have hU2 :
      ∀ j : Fin 3,
        Tendsto
          (fun r : ℝ =>
            h3SpectralScalarRawFourierSecondMass
              (W r j))
          (𝓝 s)
          (𝓝
            (h3SpectralScalarRawFourierSecondMass
              (W s j))) := by
    intro j
    have h :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_secondMass_continuousAt_time
        hν U₀ hA hU₀ hs hsR j
    change
      ContinuousAt
        (fun r : ℝ =>
          h3SpectralScalarRawFourierSecondMass
            (W r j))
        s
    simpa only [W] using h

  have hLeftTerm :
      ∀ k j : Fin 3,
        Tendsto
          (fun r : ℝ => leftTerm r k j)
          (𝓝 s)
          (𝓝 0) := by
    intro k j

    have hA :=
      (hD2 k).mul (hU0 j)

    have hB :=
      (hD0 k).mul (hU2 j)

    have hAB :=
      hA.add hB

    have hTwo :
        Tendsto
          (fun _ : ℝ => (2 : ℝ))
          (𝓝 s)
          (𝓝 2) :=
      tendsto_const_nhds

    have hTwoAB :=
      hTwo.mul hAB

    have hCoeff :
        Tendsto
          (fun _ : ℝ => (2 * Real.pi : ℝ))
          (𝓝 s)
          (𝓝 (2 * Real.pi)) :=
      tendsto_const_nhds

    have hAll :=
      hCoeff.mul hTwoAB

    dsimp only [leftTerm]
    simpa only [
      zero_mul,
      mul_zero,
      zero_add,
      add_zero
    ] using hAll

  have hRightTerm :
      ∀ k j : Fin 3,
        Tendsto
          (fun r : ℝ => rightTerm r k j)
          (𝓝 s)
          (𝓝 0) := by
    intro k j

    have hV2 :
        Tendsto
          (fun _ : ℝ =>
            h3SpectralScalarRawFourierSecondMass
              (W s k))
          (𝓝 s)
          (𝓝
            (h3SpectralScalarRawFourierSecondMass
              (W s k))) :=
      tendsto_const_nhds

    have hV0 :
        Tendsto
          (fun _ : ℝ =>
            h3SpectralScalarRawFourierL1Mass
              (W s k))
          (𝓝 s)
          (𝓝
            (h3SpectralScalarRawFourierL1Mass
              (W s k))) :=
      tendsto_const_nhds

    have hA :=
      hV2.mul (hD0 j)

    have hB :=
      hV0.mul (hD2 j)

    have hAB :=
      hA.add hB

    have hTwo :
        Tendsto
          (fun _ : ℝ => (2 : ℝ))
          (𝓝 s)
          (𝓝 2) :=
      tendsto_const_nhds

    have hTwoAB :=
      hTwo.mul hAB

    have hCoeff :
        Tendsto
          (fun _ : ℝ => (2 * Real.pi : ℝ))
          (𝓝 s)
          (𝓝 (2 * Real.pi)) :=
      tendsto_const_nhds

    have hAll :=
      hCoeff.mul hTwoAB

    dsimp only [rightTerm]
    simpa only [
      zero_mul,
      mul_zero,
      zero_add,
      add_zero
    ] using hAll

  have hLeftInner :
      ∀ k : Fin 3,
        Tendsto
          (fun r : ℝ =>
            ∑ j : Fin 3, leftTerm r k j)
          (𝓝 s)
          (𝓝 0) := by
    intro k
    simpa using
      (tendsto_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun j _ => hLeftTerm k j))

  have hRightInner :
      ∀ k : Fin 3,
        Tendsto
          (fun r : ℝ =>
            ∑ j : Fin 3, rightTerm r k j)
          (𝓝 s)
          (𝓝 0) := by
    intro k
    simpa using
      (tendsto_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun j _ => hRightTerm k j))

  have hLeftSum :
      Tendsto
        (fun r : ℝ =>
          ∑ k : Fin 3,
            ∑ j : Fin 3, leftTerm r k j)
        (𝓝 s)
        (𝓝 0) := by
    simpa using
      (tendsto_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun k _ => hLeftInner k))

  have hRightSum :
      Tendsto
        (fun r : ℝ =>
          ∑ k : Fin 3,
            ∑ j : Fin 3, rightTerm r k j)
        (𝓝 s)
        (𝓝 0) := by
    simpa using
      (tendsto_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun k _ => hRightInner k))

  have hTwo :
      Tendsto
        (fun _ : ℝ => (2 : ℝ))
        (𝓝 s)
        (𝓝 2) :=
    tendsto_const_nhds

  have hLeftScaled :=
    hTwo.mul hLeftSum

  have hRightScaled :=
    hTwo.mul hRightSum

  have hQTend0 :=
    hLeftScaled.add hRightScaled

  have hQTend :
      Tendsto Q (𝓝 s) (𝓝 0) := by
    dsimp only [Q]
    simpa only [
      mul_zero,
      zero_add
    ] using hQTend0

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hUpper :
      ∀ᶠ r in 𝓝 s,
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)
          ≤
        Q r := by
    filter_upwards [hInterval] with r hr

    have hr2 :
        ∀ k : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              ‖ξ‖ ^ 2 *
                ‖h3SpectralScalarRawFourier
                  (W r k) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro k
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMoment_integrable
          hν U₀ hA hU₀ hr.1 hr.2.le k

    have hs2 :
        ∀ k : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              ‖ξ‖ ^ 2 *
                ‖h3SpectralScalarRawFourier
                  (W s k) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro k
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMoment_integrable
          hν U₀ hA hU₀ hs hsR.le k

    have hdiff2 :
        ∀ k : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              ‖ξ‖ ^ 2 *
                ‖h3SpectralScalarRawFourier
                  ((W r - W s) k) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro k

      have hrThreeOrd :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
          3 hν U₀ hA hU₀ hr.1 hr.2.le k

      have hsThreeOrd :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
          3 hν U₀ hA hU₀ hs hsR.le k

      have hrThree :
          H3RawFourierMomentIntegrable
            (3 : ℝ) (W r k) := by
        unfold H3RawFourierMomentIntegrable
        simpa only [
          W,
          h3FourierMomentWeight_three_classicalization_cubicFrechet
        ] using hrThreeOrd

      have hsThree :
          H3RawFourierMomentIntegrable
            (3 : ℝ) (W s k) := by
        unfold H3RawFourierMomentIntegrable
        simpa only [
          W,
          h3FourierMomentWeight_three_classicalization_cubicFrechet
        ] using hsThreeOrd

      have hDiffThree :
          H3RawFourierMomentIntegrable
            (3 : ℝ)
            (W r k - W s k) :=
        h3RawFourierMomentIntegrable_three_sub
          (W r k) (W s k) hrThree hsThree

      change
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier
                (W r k - W s k) ξ‖)
          (volume : Measure H3FourierPoint3)

      exact
        h3SpectralScalarRawFourier_natMoment_integrable_le_three_of_cubic
          (W r k - W s k)
          hDiffThree
          2
          (by norm_num)

    have hBase :=
      h3RawFinLerayOuterProductDivergence_diagonal_differenceFirstMass_le_stateMasses
        (W r) (W s) i hr2 hs2 hdiff2

    dsimp only [Q, leftTerm, rightTerm]

    exact hBase

  have hNonneg :
      ∀ᶠ r in 𝓝 s,
        0 ≤
          ∫ ξ : H3FourierPoint3,
            ‖ξ‖ *
              ‖h3RawFinLerayOuterProductDivergence
                  (W r) (W r) i ξ -
                h3RawFinLerayOuterProductDivergence
                  (W s) (W s) i ξ‖ :=
    Filter.Eventually.of_forall
      (fun r =>
        integral_nonneg
          (fun ξ => by positivity))

  have hTarget :
      Tendsto
        (fun r : ℝ =>
          ∫ ξ : H3FourierPoint3,
            ‖ξ‖ *
              ‖h3RawFinLerayOuterProductDivergence
                  (W r) (W r) i ξ -
                h3RawFinLerayOuterProductDivergence
                  (W s) (W s) i ξ‖)
        (𝓝 s)
        (𝓝 0) :=
    squeeze_zero'
      hNonneg
      hUpper
      hQTend

  simpa only [W] using hTarget

end

end Euclidean
end Bridge
end PrimeTensor
