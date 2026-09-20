import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Second.Difference.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.First.Difference.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Third.Seed

/-!
# Classicalization: selected forcing second-moment time continuity

The order-two forcing-difference bound from the preceding checkpoint has four
types of factors:

* cubic mass of the selected state difference;
* raw `L¹` mass of the selected state difference;
* cubic mass of the selected state itself;
* raw `L¹` mass of the selected state itself.

At a strict positive interior restart time, the first two difference masses
tend to zero.  The state factors need not be separately rebuilt as continuous
functions here: the existing positive-time cubic slab and restart-wide raw
`L¹` envelope bound them uniformly on one neighborhood of the base time.

Consequently

    ∫ |ξ|² |N(W(r),W(r)) - N(W(s),W(s))| dξ → 0.

This is the moving-state input needed for the fresh second-Fréchet Duhamel
endpoint.  No new convolution or heat estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingSecondDifferenceContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The second weighted raw Fourier mass of the selected instantaneous forcing
difference tends to zero at every strict positive interior restart time. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_differenceSecondMass_tendsto_zero
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
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)
      (𝓝 s)
      (𝓝 0) := by
  dsimp only

  let R₀ : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let a : ℝ := s / 2
  let b : ℝ := (s + R₀) / 2

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let M0 : ℝ :=
    h3SelectedRestartRawFourierL1Envelope A

  let M3 : ℝ :=
    h3SelectedMildThirdMomentUniformEnvelope ν A a b

  have hR₀ : 0 < R₀ := by
    dsimp only [R₀]
    exact h3FinHeatLerayRestartRadius_pos ν hA

  have hsR₀ : s < R₀ := by
    simpa only [R₀] using hsR

  have ha : 0 < a := by
    dsimp only [a]
    linarith

  have has : a < s := by
    dsimp only [a]
    linarith

  have hsb : s < b := by
    dsimp only [b, R₀]
    linarith

  have hab : a < b := by
    exact has.trans hsb

  have hbR₀ : b ≤ R₀ := by
    dsimp only [b]
    linarith

  have hM0 : 0 ≤ M0 := by
    dsimp only [M0]
    exact h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM3 : 0 ≤ M3 := by
    dsimp only [M3]
    exact
      h3SelectedMildThirdMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha hab hbR₀

  let leftTerm : ℝ → Fin 3 → Fin 3 → ℝ :=
    fun r k j =>
      (2 * Real.pi) *
        (h3FourierThirdSplitCoefficient *
          (h3SpectralScalarRawFourierThirdMass
                ((W r - W s) k) * M0 +
            h3SpectralScalarRawFourierL1Mass
                ((W r - W s) k) * M3))

  let rightTerm : ℝ → Fin 3 → Fin 3 → ℝ :=
    fun r k j =>
      (2 * Real.pi) *
        (h3FourierThirdSplitCoefficient *
          (M3 *
              h3SpectralScalarRawFourierL1Mass
                ((W r - W s) j) +
            M0 *
              h3SpectralScalarRawFourierThirdMass
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

  have hD3 :
      ∀ k : Fin 3,
        Tendsto
          (fun r : ℝ =>
            h3SpectralScalarRawFourierThirdMass
              ((W r - W s) k))
          (𝓝 s)
          (𝓝 0) := by
    intro k
    have h :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_cubicDifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR k
    change
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierThirdMass
            (W r k - W s k))
        (𝓝 s)
        (𝓝 0)
    simpa only [
      W,
      h3SpectralScalarRawFourierMomentMass_three_eq
    ] using h

  have hLeftTerm :
      ∀ k j : Fin 3,
        Tendsto
          (fun r : ℝ => leftTerm r k j)
          (𝓝 s)
          (𝓝 0) := by
    intro k j

    have hM0Const :
        Tendsto
          (fun _ : ℝ => M0)
          (𝓝 s)
          (𝓝 M0) :=
      tendsto_const_nhds

    have hM3Const :
        Tendsto
          (fun _ : ℝ => M3)
          (𝓝 s)
          (𝓝 M3) :=
      tendsto_const_nhds

    have hA :=
      (hD3 k).mul hM0Const

    have hB :=
      (hD0 k).mul hM3Const

    have hAB :=
      hA.add hB

    have hSplit :
        Tendsto
          (fun _ : ℝ => h3FourierThirdSplitCoefficient)
          (𝓝 s)
          (𝓝 h3FourierThirdSplitCoefficient) :=
      tendsto_const_nhds

    have hWeighted :=
      hSplit.mul hAB

    have hCoeff :
        Tendsto
          (fun _ : ℝ => (2 * Real.pi : ℝ))
          (𝓝 s)
          (𝓝 (2 * Real.pi)) :=
      tendsto_const_nhds

    have hAll :=
      hCoeff.mul hWeighted

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

    have hM0Const :
        Tendsto
          (fun _ : ℝ => M0)
          (𝓝 s)
          (𝓝 M0) :=
      tendsto_const_nhds

    have hM3Const :
        Tendsto
          (fun _ : ℝ => M3)
          (𝓝 s)
          (𝓝 M3) :=
      tendsto_const_nhds

    have hA :=
      hM3Const.mul (hD0 j)

    have hB :=
      hM0Const.mul (hD3 j)

    have hAB :=
      hA.add hB

    have hSplit :
        Tendsto
          (fun _ : ℝ => h3FourierThirdSplitCoefficient)
          (𝓝 s)
          (𝓝 h3FourierThirdSplitCoefficient) :=
      tendsto_const_nhds

    have hWeighted :=
      hSplit.mul hAB

    have hCoeff :
        Tendsto
          (fun _ : ℝ => (2 * Real.pi : ℝ))
          (𝓝 s)
          (𝓝 (2 * Real.pi)) :=
      tendsto_const_nhds

    have hAll :=
      hCoeff.mul hWeighted

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

  have hQTend0 :=
    (hTwo.mul hLeftSum).add
      (hTwo.mul hRightSum)

  have hQTend :
      Tendsto Q (𝓝 s) (𝓝 0) := by
    dsimp only [Q]
    simpa only [
      mul_zero,
      zero_add
    ] using hQTend0

  have hInterval :
      Set.Ioo a b ∈ 𝓝 s :=
    Ioo_mem_nhds has hsb

  have hUpper :
      ∀ᶠ r in 𝓝 s,
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)
          ≤
        Q r := by
    filter_upwards [hInterval] with r hr

    have hr3 :
        ∀ k : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              ‖ξ‖ ^ 3 *
                ‖h3SpectralScalarRawFourier
                  (W r k) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro k
      have hr0 : 0 < r :=
        lt_trans ha hr.1
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMoment_integrable
          hν U₀ hA hU₀ hr0 (le_trans hr.2.le hbR₀) k

    have hs3 :
        ∀ k : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              ‖ξ‖ ^ 3 *
                ‖h3SpectralScalarRawFourier
                  (W s k) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro k
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMoment_integrable
          hν U₀ hA hU₀ hs hsR.le k

    have hdiff3 :
        ∀ k : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              ‖ξ‖ ^ 3 *
                ‖h3SpectralScalarRawFourier
                  ((W r - W s) k) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro k

      have hrThree :
          H3RawFourierMomentIntegrable
            (3 : ℝ) (W r k) := by
        unfold H3RawFourierMomentIntegrable
        simpa only [h3FourierMomentWeight_three] using hr3 k

      have hsThree :
          H3RawFourierMomentIntegrable
            (3 : ℝ) (W s k) := by
        unfold H3RawFourierMomentIntegrable
        simpa only [h3FourierMomentWeight_three] using hs3 k

      have hDiffThree :
          H3RawFourierMomentIntegrable
            (3 : ℝ)
            (W r k - W s k) :=
        h3RawFourierMomentIntegrable_three_sub
          (W r k) (W s k) hrThree hsThree

      unfold H3RawFourierMomentIntegrable at hDiffThree

      change
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier
                (W r k - W s k) ξ‖)
          (volume : Measure H3FourierPoint3)

      simpa only [
        h3FourierMomentWeight_three
      ] using hDiffThree

    have hBase :=
      h3RawFinLerayOuterProductDivergence_diagonal_differenceSecondMass_le_stateMasses
        (W r) (W s) i hr3 hs3 hdiff3

    have hr0 :
        ∀ j : Fin 3,
          h3SpectralScalarRawFourierL1Mass (W r j) ≤ M0 := by
      intro j
      dsimp only [M0, W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
          hν U₀ hA hU₀ r j

    have hs0 :
        ∀ k : Fin 3,
          h3SpectralScalarRawFourierL1Mass (W s k) ≤ M0 := by
      intro k
      dsimp only [M0, W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
          hν U₀ hA hU₀ s k

    have hrM3 :
        ∀ j : Fin 3,
          h3SpectralScalarRawFourierThirdMass (W r j) ≤ M3 := by
      intro j
      dsimp only [M3, W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMass_le_uniform_on
          hν U₀ hA hU₀
          ha hr.1.le hr.2.le hbR₀ j

    have hsM3 :
        ∀ k : Fin 3,
          h3SpectralScalarRawFourierThirdMass (W s k) ≤ M3 := by
      intro k
      dsimp only [M3, W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMass_le_uniform_on
          hν U₀ hA hU₀
          ha has.le hsb.le hbR₀ k

    have hCoeff0 : 0 ≤ 2 * Real.pi := by positivity

    have hSplit0 : 0 ≤ h3FourierThirdSplitCoefficient := by
      unfold h3FourierThirdSplitCoefficient
      norm_num

    have hLeftTermLe :
        ∀ k j : Fin 3,
          (2 * Real.pi) *
              (h3FourierThirdSplitCoefficient *
                (h3SpectralScalarRawFourierThirdMass
                      ((W r - W s) k) *
                    h3SpectralScalarRawFourierL1Mass (W r j) +
                  h3SpectralScalarRawFourierL1Mass
                      ((W r - W s) k) *
                    h3SpectralScalarRawFourierThirdMass (W r j)))
            ≤
          leftTerm r k j := by
      intro k j

      have hD3nonneg :
          0 ≤
            h3SpectralScalarRawFourierThirdMass
              ((W r - W s) k) :=
        h3SpectralScalarRawFourierThirdMass_nonneg
          ((W r - W s) k)

      have hD0nonneg :
          0 ≤
            h3SpectralScalarRawFourierL1Mass
              ((W r - W s) k) :=
        h3SpectralScalarRawFourierL1Mass_nonneg
          ((W r - W s) k)

      have hA :
          h3SpectralScalarRawFourierThirdMass
                ((W r - W s) k) *
              h3SpectralScalarRawFourierL1Mass (W r j)
            ≤
          h3SpectralScalarRawFourierThirdMass
                ((W r - W s) k) * M0 :=
        mul_le_mul_of_nonneg_left
          (hr0 j) hD3nonneg

      have hB :
          h3SpectralScalarRawFourierL1Mass
                ((W r - W s) k) *
              h3SpectralScalarRawFourierThirdMass (W r j)
            ≤
          h3SpectralScalarRawFourierL1Mass
                ((W r - W s) k) * M3 :=
        mul_le_mul_of_nonneg_left
          (hrM3 j) hD0nonneg

      dsimp only [leftTerm]

      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (add_le_add hA hB)
            hSplit0)
          hCoeff0

    have hRightTermLe :
        ∀ k j : Fin 3,
          (2 * Real.pi) *
              (h3FourierThirdSplitCoefficient *
                (h3SpectralScalarRawFourierThirdMass (W s k) *
                    h3SpectralScalarRawFourierL1Mass
                      ((W r - W s) j) +
                  h3SpectralScalarRawFourierL1Mass (W s k) *
                    h3SpectralScalarRawFourierThirdMass
                      ((W r - W s) j)))
            ≤
          rightTerm r k j := by
      intro k j

      have hD0nonneg :
          0 ≤
            h3SpectralScalarRawFourierL1Mass
              ((W r - W s) j) :=
        h3SpectralScalarRawFourierL1Mass_nonneg
          ((W r - W s) j)

      have hD3nonneg :
          0 ≤
            h3SpectralScalarRawFourierThirdMass
              ((W r - W s) j) :=
        h3SpectralScalarRawFourierThirdMass_nonneg
          ((W r - W s) j)

      have hA :
          h3SpectralScalarRawFourierThirdMass (W s k) *
              h3SpectralScalarRawFourierL1Mass
                ((W r - W s) j)
            ≤
          M3 *
              h3SpectralScalarRawFourierL1Mass
                ((W r - W s) j) :=
        mul_le_mul_of_nonneg_right
          (hsM3 k) hD0nonneg

      have hB :
          h3SpectralScalarRawFourierL1Mass (W s k) *
              h3SpectralScalarRawFourierThirdMass
                ((W r - W s) j)
            ≤
          M0 *
              h3SpectralScalarRawFourierThirdMass
                ((W r - W s) j) :=
        mul_le_mul_of_nonneg_right
          (hs0 k) hD3nonneg

      dsimp only [rightTerm]

      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (add_le_add hA hB)
            hSplit0)
          hCoeff0

    have hLeftSumLe :
        (∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3FourierThirdSplitCoefficient *
                (h3SpectralScalarRawFourierThirdMass
                      ((W r - W s) k) *
                    h3SpectralScalarRawFourierL1Mass (W r j) +
                  h3SpectralScalarRawFourierL1Mass
                      ((W r - W s) k) *
                    h3SpectralScalarRawFourierThirdMass (W r j))))
          ≤
        ∑ k : Fin 3,
          ∑ j : Fin 3, leftTerm r k j :=
      Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun j _ =>
          hLeftTermLe k j

    have hRightSumLe :
        (∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3FourierThirdSplitCoefficient *
                (h3SpectralScalarRawFourierThirdMass (W s k) *
                    h3SpectralScalarRawFourierL1Mass
                      ((W r - W s) j) +
                  h3SpectralScalarRawFourierL1Mass (W s k) *
                    h3SpectralScalarRawFourierThirdMass
                      ((W r - W s) j))))
          ≤
        ∑ k : Fin 3,
          ∑ j : Fin 3, rightTerm r k j :=
      Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun j _ =>
          hRightTermLe k j

    have hBoundToQ :
        2 *
            (∑ k : Fin 3,
              ∑ j : Fin 3,
                (2 * Real.pi) *
                  (h3FourierThirdSplitCoefficient *
                    (h3SpectralScalarRawFourierThirdMass
                          ((W r - W s) k) *
                        h3SpectralScalarRawFourierL1Mass (W r j) +
                      h3SpectralScalarRawFourierL1Mass
                          ((W r - W s) k) *
                        h3SpectralScalarRawFourierThirdMass (W r j))))
          +
          2 *
            (∑ k : Fin 3,
              ∑ j : Fin 3,
                (2 * Real.pi) *
                  (h3FourierThirdSplitCoefficient *
                    (h3SpectralScalarRawFourierThirdMass (W s k) *
                        h3SpectralScalarRawFourierL1Mass
                          ((W r - W s) j) +
                      h3SpectralScalarRawFourierL1Mass (W s k) *
                        h3SpectralScalarRawFourierThirdMass
                          ((W r - W s) j))))
            ≤
          Q r := by
      dsimp only [Q]
      exact
        add_le_add
          (mul_le_mul_of_nonneg_left hLeftSumLe (by norm_num))
          (mul_le_mul_of_nonneg_left hRightSumLe (by norm_num))

    exact
      hBase.trans hBoundToQ

  have hNonneg :
      ∀ᶠ r in 𝓝 s,
        0 ≤
          ∫ ξ : H3FourierPoint3,
            ‖ξ‖ ^ 2 *
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
            ‖ξ‖ ^ 2 *
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
