import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Third.Difference.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.First.Difference.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quartic.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quartic.Frechet.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Uniform.Fourth.Moment.Envelope

/-!
# Classicalization: selected forcing cubic-moment time continuity

The preceding checkpoint bounds the cubic weighted raw-Fourier mass of the
diagonal forcing difference by products of:

* fourth mass of the selected state difference;
* raw `L¹` mass of the selected state difference;
* fourth mass of the selected state;
* raw `L¹` mass of the selected state.

At every strict positive interior restart time, the first two difference
masses tend to zero.  The state factors are uniformly bounded on one closed
positive neighborhood by the existing fourth-moment and raw-`L¹` envelopes.

Consequently

    ∫ |ξ|³ |N(W(r),W(r)) - N(W(s),W(s))| dξ → 0.

No new nonlinear or heat estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingThirdDifferenceContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- The cubic weighted raw Fourier mass of the selected instantaneous forcing
difference tends to zero at every strict positive interior restart time. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_differenceThirdMass_tendsto_zero
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
          ‖ξ‖ ^ 3 *
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

  let M4 : ℝ :=
    h3SelectedMildFourthMomentUniformEnvelope ν A a b

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

  have hab : a < b :=
    has.trans hsb

  have hbR₀ : b ≤ R₀ := by
    dsimp only [b]
    linarith

  have hM0 : 0 ≤ M0 := by
    dsimp only [M0]
    exact h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM4 : 0 ≤ M4 := by
    dsimp only [M4]
    exact
      h3SelectedMildFourthMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha hab hbR₀

  let leftTerm : ℝ → Fin 3 → Fin 3 → ℝ :=
    fun r k j =>
      (2 * Real.pi) *
        (h3FourierFourthSplitCoefficient *
          (h3SpectralScalarRawFourierFourthMass
                ((W r - W s) k) * M0 +
            h3SpectralScalarRawFourierL1Mass
                ((W r - W s) k) * M4))

  let rightTerm : ℝ → Fin 3 → Fin 3 → ℝ :=
    fun r k j =>
      (2 * Real.pi) *
        (h3FourierFourthSplitCoefficient *
          (M4 *
              h3SpectralScalarRawFourierL1Mass
                ((W r - W s) j) +
            M0 *
              h3SpectralScalarRawFourierFourthMass
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

  have hD4 :
      ∀ k : Fin 3,
        Tendsto
          (fun r : ℝ =>
            h3SpectralScalarRawFourierFourthMass
              ((W r - W s) k))
          (𝓝 s)
          (𝓝 0) := by
    intro k
    have h :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_quarticDifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR k

    change
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierFourthMass
            (W r k - W s k))
        (𝓝 s)
        (𝓝 0)

    unfold h3SpectralScalarRawFourierFourthMass
    unfold h3SpectralScalarRawFourierMomentMass at h

    simpa only [
      h3FourierMomentWeight_four_classicalization_quarticFrechet
    ] using h

  have hLeftTerm :
      ∀ k j : Fin 3,
        Tendsto
          (fun r : ℝ => leftTerm r k j)
          (𝓝 s)
          (𝓝 0) := by
    intro k j

    have hM0Const :
        Tendsto (fun _ : ℝ => M0) (𝓝 s) (𝓝 M0) :=
      tendsto_const_nhds

    have hM4Const :
        Tendsto (fun _ : ℝ => M4) (𝓝 s) (𝓝 M4) :=
      tendsto_const_nhds

    have hA :=
      (hD4 k).mul hM0Const

    have hB :=
      (hD0 k).mul hM4Const

    have hAB :=
      hA.add hB

    have hSplit :
        Tendsto
          (fun _ : ℝ => h3FourierFourthSplitCoefficient)
          (𝓝 s)
          (𝓝 h3FourierFourthSplitCoefficient) :=
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
        Tendsto (fun _ : ℝ => M0) (𝓝 s) (𝓝 M0) :=
      tendsto_const_nhds

    have hM4Const :
        Tendsto (fun _ : ℝ => M4) (𝓝 s) (𝓝 M4) :=
      tendsto_const_nhds

    have hA :=
      hM4Const.mul (hD0 j)

    have hB :=
      hM0Const.mul (hD4 j)

    have hAB :=
      hA.add hB

    have hSplit :
        Tendsto
          (fun _ : ℝ => h3FourierFourthSplitCoefficient)
          (𝓝 s)
          (𝓝 h3FourierFourthSplitCoefficient) :=
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
    simpa only [mul_zero, zero_add] using hQTend0

  have hInterval :
      Set.Ioo a b ∈ 𝓝 s :=
    Ioo_mem_nhds has hsb

  have hUpper :
      ∀ᶠ r in 𝓝 s,
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)
          ≤
        Q r := by
    filter_upwards [hInterval] with r hr

    have hr4 :
        ∀ k : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              ‖ξ‖ ^ 4 *
                ‖h3SpectralScalarRawFourier
                  (W r k) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro k
      have hr0 : 0 < r :=
        lt_trans ha hr.1
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
          4 hν U₀ hA hU₀ hr0 (le_trans hr.2.le hbR₀) k

    have hs4 :
        ∀ k : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              ‖ξ‖ ^ 4 *
                ‖h3SpectralScalarRawFourier
                  (W s k) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro k
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
          4 hν U₀ hA hU₀ hs hsR.le k

    have hdiff4 :
        ∀ k : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              ‖ξ‖ ^ 4 *
                ‖h3SpectralScalarRawFourier
                  ((W r - W s) k) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro k

      have hrFour :
          H3RawFourierMomentIntegrable
            (4 : ℝ) (W r k) := by
        unfold H3RawFourierMomentIntegrable
        simpa only [
          h3FourierMomentWeight_four_classicalization_quarticFrechet
        ] using hr4 k

      have hsFour :
          H3RawFourierMomentIntegrable
            (4 : ℝ) (W s k) := by
        unfold H3RawFourierMomentIntegrable
        simpa only [
          h3FourierMomentWeight_four_classicalization_quarticFrechet
        ] using hs4 k

      have hDiffFour :
          H3RawFourierMomentIntegrable
            (4 : ℝ) (W r k - W s k) :=
        h3RawFourierMomentIntegrable_four_sub
          (W r k) (W s k) hrFour hsFour

      unfold H3RawFourierMomentIntegrable at hDiffFour

      change
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier
                (W r k - W s k) ξ‖)
          (volume : Measure H3FourierPoint3)

      simpa only [
        h3FourierMomentWeight_four_classicalization_quarticFrechet
      ] using hDiffFour

    have hBase :=
      h3RawFinLerayOuterProductDivergence_diagonal_differenceThirdMass_le_stateMasses
        (W r) (W s) i hr4 hs4 hdiff4

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

    have hrM4 :
        ∀ j : Fin 3,
          h3SpectralScalarRawFourierFourthMass (W r j) ≤ M4 := by
      intro j
      dsimp only [M4, W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMass_le_uniform_on
          hν U₀ hA hU₀
          ha hr.1.le hr.2.le hbR₀ j

    have hsM4 :
        ∀ k : Fin 3,
          h3SpectralScalarRawFourierFourthMass (W s k) ≤ M4 := by
      intro k
      dsimp only [M4, W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMass_le_uniform_on
          hν U₀ hA hU₀
          ha has.le hsb.le hbR₀ k

    have hCoeff0 : 0 ≤ 2 * Real.pi := by positivity

    have hSplit0 : 0 ≤ h3FourierFourthSplitCoefficient := by
      exact h3FourierFourthSplitCoefficient_nonneg

    have hLeftTermLe :
        ∀ k j : Fin 3,
          (2 * Real.pi) *
              (h3FourierFourthSplitCoefficient *
                (h3SpectralScalarRawFourierFourthMass
                      ((W r - W s) k) *
                    h3SpectralScalarRawFourierL1Mass (W r j) +
                  h3SpectralScalarRawFourierL1Mass
                      ((W r - W s) k) *
                    h3SpectralScalarRawFourierFourthMass (W r j)))
            ≤
          leftTerm r k j := by
      intro k j

      have hD4nonneg :
          0 ≤
            h3SpectralScalarRawFourierFourthMass
              ((W r - W s) k) :=
        h3SpectralScalarRawFourierFourthMass_nonneg
          ((W r - W s) k)

      have hD0nonneg :
          0 ≤
            h3SpectralScalarRawFourierL1Mass
              ((W r - W s) k) :=
        h3SpectralScalarRawFourierL1Mass_nonneg
          ((W r - W s) k)

      have hA :
          h3SpectralScalarRawFourierFourthMass
                ((W r - W s) k) *
              h3SpectralScalarRawFourierL1Mass (W r j)
            ≤
          h3SpectralScalarRawFourierFourthMass
                ((W r - W s) k) * M0 :=
        mul_le_mul_of_nonneg_left
          (hr0 j) hD4nonneg

      have hB :
          h3SpectralScalarRawFourierL1Mass
                ((W r - W s) k) *
              h3SpectralScalarRawFourierFourthMass (W r j)
            ≤
          h3SpectralScalarRawFourierL1Mass
                ((W r - W s) k) * M4 :=
        mul_le_mul_of_nonneg_left
          (hrM4 j) hD0nonneg

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
              (h3FourierFourthSplitCoefficient *
                (h3SpectralScalarRawFourierFourthMass (W s k) *
                    h3SpectralScalarRawFourierL1Mass
                      ((W r - W s) j) +
                  h3SpectralScalarRawFourierL1Mass (W s k) *
                    h3SpectralScalarRawFourierFourthMass
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

      have hD4nonneg :
          0 ≤
            h3SpectralScalarRawFourierFourthMass
              ((W r - W s) j) :=
        h3SpectralScalarRawFourierFourthMass_nonneg
          ((W r - W s) j)

      have hA :
          h3SpectralScalarRawFourierFourthMass (W s k) *
              h3SpectralScalarRawFourierL1Mass
                ((W r - W s) j)
            ≤
          M4 *
              h3SpectralScalarRawFourierL1Mass
                ((W r - W s) j) :=
        mul_le_mul_of_nonneg_right
          (hsM4 k) hD0nonneg

      have hB :
          h3SpectralScalarRawFourierL1Mass (W s k) *
              h3SpectralScalarRawFourierFourthMass
                ((W r - W s) j)
            ≤
          M0 *
              h3SpectralScalarRawFourierFourthMass
                ((W r - W s) j) :=
        mul_le_mul_of_nonneg_right
          (hs0 k) hD4nonneg

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
              (h3FourierFourthSplitCoefficient *
                (h3SpectralScalarRawFourierFourthMass
                      ((W r - W s) k) *
                    h3SpectralScalarRawFourierL1Mass (W r j) +
                  h3SpectralScalarRawFourierL1Mass
                      ((W r - W s) k) *
                    h3SpectralScalarRawFourierFourthMass (W r j))))
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
              (h3FourierFourthSplitCoefficient *
                (h3SpectralScalarRawFourierFourthMass (W s k) *
                    h3SpectralScalarRawFourierL1Mass
                      ((W r - W s) j) +
                  h3SpectralScalarRawFourierL1Mass (W s k) *
                    h3SpectralScalarRawFourierFourthMass
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
                  (h3FourierFourthSplitCoefficient *
                    (h3SpectralScalarRawFourierFourthMass
                          ((W r - W s) k) *
                        h3SpectralScalarRawFourierL1Mass (W r j) +
                      h3SpectralScalarRawFourierL1Mass
                          ((W r - W s) k) *
                        h3SpectralScalarRawFourierFourthMass (W r j))))
          +
          2 *
            (∑ k : Fin 3,
              ∑ j : Fin 3,
                (2 * Real.pi) *
                  (h3FourierFourthSplitCoefficient *
                    (h3SpectralScalarRawFourierFourthMass (W s k) *
                        h3SpectralScalarRawFourierL1Mass
                          ((W r - W s) j) +
                      h3SpectralScalarRawFourierL1Mass (W s k) *
                        h3SpectralScalarRawFourierFourthMass
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
            ‖ξ‖ ^ 3 *
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
            ‖ξ‖ ^ 3 *
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
