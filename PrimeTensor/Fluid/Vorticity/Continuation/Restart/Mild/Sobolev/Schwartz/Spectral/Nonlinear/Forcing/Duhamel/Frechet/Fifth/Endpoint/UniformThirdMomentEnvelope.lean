import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarterMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdMildMass

/-!
# Fifth Fréchet endpoint: uniform positive-time third state envelope

The fifth layer now needs one cubic state-moment constant valid throughout a
fixed positive interval `[a,t]`.

The pointwise third-moment envelope contains one inherited nested interval
quantity: the full-third variation coefficient uses the already-uniform
`9/4` state envelope on `(r/2,r)`.  This file first proves the three exact
half-interval nesting facts needed to enlarge

    (r/2,r) ⊂ (a/2,t),

namely for

* the uniform second state envelope;
* the uniform quarter forcing envelope;
* the uniform `9/4` state envelope.

Those scalar comparisons then uniformize every term of the selected cubic
state estimate:

* free cubic heat at the lower endpoint `a`;
* midpoint-head cubic heat at `a/2`, with H³ size at `t`;
* varying terminal tail with the global `9/4` envelope on `(a/2,t)`;
* frozen terminal tail with the uniform first forcing envelope on `[a,t]`.

No new PDE estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointUniformThirdMoment
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The cubic positive-time heat coefficient is antitone. -/
theorem h3HeatThirdMomentRawL1Coefficient_antitone_pos
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hab : a ≤ b) :
    h3HeatThirdMomentRawL1Coefficient ν b
      ≤
    h3HeatThirdMomentRawL1Coefficient ν a := by
  have hArg :
      ν * (a / 3) ≤ ν * (b / 3) := by
    nlinarith

  have hSqrt :
      Real.sqrt (ν * (a / 3))
        ≤
      Real.sqrt (ν * (b / 3)) :=
    Real.sqrt_le_sqrt hArg

  have hSqrtA :
      0 < Real.sqrt (ν * (a / 3)) :=
    Real.sqrt_pos.2 (by positivity)

  have hInv :
      (Real.sqrt (ν * (b / 3)))⁻¹
        ≤
      (Real.sqrt (ν * (a / 3)))⁻¹ :=
    inv_anti₀ hSqrtA hSqrt

  unfold h3HeatThirdMomentRawL1Coefficient
  gcongr

/-- The already-uniform selected second-moment envelope respects the nested
half intervals `(r/2,r) ⊂ (a/2,t)`. -/
theorem h3SelectedMildSecondMomentUniformEnvelope_halfInterval_le
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedMildSecondMomentUniformEnvelope ν A (r / 2) r
      ≤
    h3SelectedMildSecondMomentUniformEnvelope ν A (a / 2) t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have ht : 0 < t :=
    lt_of_lt_of_le hr hrt

  have ha2 : 0 < a / 2 := by positivity
  have ha4 : 0 < a / 2 / 2 := by positivity

  have hBase2 : a / 2 ≤ r / 2 := by linarith
  have hBase4 : a / 2 / 2 ≤ r / 2 / 2 := by linarith
  have hHalfTime : r / 2 ≤ t / 2 := by linarith

  have hCFree :
      h3HeatSecondMomentRawL1Coefficient ν (r / 2)
        ≤
      h3HeatSecondMomentRawL1Coefficient ν (a / 2) :=
    h3HeatSecondMomentRawL1Coefficient_antitone_pos
      hν ha2 hBase2

  have hCHead :
      h3HeatSecondMomentRawL1Coefficient ν (r / 2 / 2)
        ≤
      h3HeatSecondMomentRawL1Coefficient ν (a / 2 / 2) :=
    h3HeatSecondMomentRawL1Coefficient_antitone_pos
      hν ha4 hBase4

  have hH3 :
      h3SelectedDuhamelHalfTimeH3Envelope ν A r
        ≤
      h3SelectedDuhamelHalfTimeH3Envelope ν A t :=
    h3SelectedDuhamelHalfTimeH3Envelope_mono
      hA hr.le hrt

  have hCdw0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient :=
    h3RawFourierL1DeweightingCoefficient_nonneg

  have hFreeFactor0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient * A :=
    mul_nonneg hCdw0 hA

  have hFree :
      h3HeatSecondMomentRawL1Coefficient ν (r / 2) *
          h3RawFourierL1DeweightingCoefficient * A
        ≤
      h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
          h3RawFourierL1DeweightingCoefficient * A := by
    calc
      h3HeatSecondMomentRawL1Coefficient ν (r / 2) *
            h3RawFourierL1DeweightingCoefficient * A
          =
        h3HeatSecondMomentRawL1Coefficient ν (r / 2) *
          (h3RawFourierL1DeweightingCoefficient * A) := by ring
      _ ≤
        h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
          (h3RawFourierL1DeweightingCoefficient * A) :=
        mul_le_mul_of_nonneg_right hCFree hFreeFactor0
      _ =
        h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
          h3RawFourierL1DeweightingCoefficient * A := by ring

  have hH3r0 :
      0 ≤ h3SelectedDuhamelHalfTimeH3Envelope ν A r :=
    h3SelectedDuhamelHalfTimeH3Envelope_nonneg hA

  have hCHeadUpper0 :
      0 ≤ h3HeatSecondMomentRawL1Coefficient ν (a / 2 / 2) :=
    h3HeatSecondMomentRawL1Coefficient_nonneg _ _

  have hHead :
      h3HeatSecondMomentRawL1Coefficient ν (r / 2 / 2) *
          h3RawFourierL1DeweightingCoefficient *
          h3SelectedDuhamelHalfTimeH3Envelope ν A r
        ≤
      h3HeatSecondMomentRawL1Coefficient ν (a / 2 / 2) *
          h3RawFourierL1DeweightingCoefficient *
          h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
    calc
      h3HeatSecondMomentRawL1Coefficient ν (r / 2 / 2) *
            h3RawFourierL1DeweightingCoefficient *
            h3SelectedDuhamelHalfTimeH3Envelope ν A r
          ≤
        h3HeatSecondMomentRawL1Coefficient ν (a / 2 / 2) *
            h3RawFourierL1DeweightingCoefficient *
            h3SelectedDuhamelHalfTimeH3Envelope ν A r := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCHead hCdw0)
            hH3r0
      _ ≤
        h3HeatSecondMomentRawL1Coefficient ν (a / 2 / 2) *
            h3RawFourierL1DeweightingCoefficient *
            h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
        exact
          mul_le_mul_of_nonneg_left
            hH3
            (mul_nonneg hCHeadUpper0 hCdw0)

  have hMass0 :
      0 ≤ 4 * h3NonlinearForcingL1Coefficient * A ^ 2 := by
    have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
      h3NonlinearForcingL1Coefficient_nonneg
    positivity

  have hTailHeadCoeff :
      h3HeatSecondMomentRawL1Coefficient ν (r / 2 / 2) *
          (4 * h3NonlinearForcingL1Coefficient * A ^ 2)
        ≤
      h3HeatSecondMomentRawL1Coefficient ν (a / 2 / 2) *
          (4 * h3NonlinearForcingL1Coefficient * A ^ 2) :=
    mul_le_mul_of_nonneg_right hCHead hMass0

  have hTailHeadCoeff0 :
      0 ≤
        h3HeatSecondMomentRawL1Coefficient ν (r / 2 / 2) *
          (4 * h3NonlinearForcingL1Coefficient * A ^ 2) :=
    mul_nonneg
      (h3HeatSecondMomentRawL1Coefficient_nonneg _ _)
      hMass0

  have hTailHead :
      (r / 2) *
          (h3HeatSecondMomentRawL1Coefficient ν (r / 2 / 2) *
            (4 * h3NonlinearForcingL1Coefficient * A ^ 2))
        ≤
      (t / 2) *
          (h3HeatSecondMomentRawL1Coefficient ν (a / 2 / 2) *
            (4 * h3NonlinearForcingL1Coefficient * A ^ 2)) := by
    calc
      (r / 2) *
          (h3HeatSecondMomentRawL1Coefficient ν (r / 2 / 2) *
            (4 * h3NonlinearForcingL1Coefficient * A ^ 2))
          ≤
        (t / 2) *
          (h3HeatSecondMomentRawL1Coefficient ν (r / 2 / 2) *
            (4 * h3NonlinearForcingL1Coefficient * A ^ 2)) :=
        mul_le_mul_of_nonneg_right hHalfTime hTailHeadCoeff0
      _ ≤
        (t / 2) *
          (h3HeatSecondMomentRawL1Coefficient ν (a / 2 / 2) *
            (4 * h3NonlinearForcingL1Coefficient * A ^ 2)) :=
        mul_le_mul_of_nonneg_left hTailHeadCoeff (by positivity)

  have hLocal :
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (r / 2 / 2) r
        ≤
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (a / 2 / 2) t :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_interval_mono
      hν hA ha4 hBase4 hr.le hrt

  have hLocalUpper0 :
      0 ≤
        h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (a / 2 / 2) t :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_nonneg
      hν.le hA ht.le

  have hLag0 : 0 ≤ r - r / 2 := by linarith
  have hLag : r - r / 2 ≤ t - t / 2 := by linarith

  have hPow :
      (r - r / 2) ^ ((1 : ℝ) / 4)
        ≤
      (t - t / 2) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hLag0 hLag (by norm_num)

  have hPow0 :
      0 ≤ (r - r / 2) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hLag0 _

  have hLocalPow :
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (r / 2 / 2) r *
          (r - r / 2) ^ ((1 : ℝ) / 4)
        ≤
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (a / 2 / 2) t *
          (t - t / 2) ^ ((1 : ℝ) / 4) := by
    calc
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (r / 2 / 2) r *
            (r - r / 2) ^ ((1 : ℝ) / 4)
          ≤
        h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (a / 2 / 2) t *
            (r - r / 2) ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hLocal hPow0
      _ ≤
        h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (a / 2 / 2) t *
            (t - t / 2) ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hPow hLocalUpper0

  have hVariation :
      12 * ν⁻¹ *
          h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (r / 2 / 2) r *
          (r - r / 2) ^ ((1 : ℝ) / 4)
        ≤
      12 * ν⁻¹ *
          h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (a / 2 / 2) t *
          (t - t / 2) ^ ((1 : ℝ) / 4) := by
    have hScale0 : 0 ≤ 12 * ν⁻¹ := by positivity
    calc
      12 * ν⁻¹ *
            h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
              ν A (r / 2 / 2) r *
            (r - r / 2) ^ ((1 : ℝ) / 4)
          =
        (12 * ν⁻¹) *
          (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
              ν A (r / 2 / 2) r *
            (r - r / 2) ^ ((1 : ℝ) / 4)) := by ring
      _ ≤
        (12 * ν⁻¹) *
          (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
              ν A (a / 2 / 2) t *
            (t - t / 2) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hLocalPow hScale0
      _ =
        12 * ν⁻¹ *
          h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (a / 2 / 2) t *
          (t - t / 2) ^ ((1 : ℝ) / 4) := by ring

  have hFrozenRefl :
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
          (4 * h3NonlinearForcingL1Coefficient * A ^ 2)
        ≤
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
          (4 * h3NonlinearForcingL1Coefficient * A ^ 2) :=
    le_rfl

  have hTail :
      h3SelectedDuhamelTailSecondMomentUniformEnvelope ν A (r / 2) r
        ≤
      h3SelectedDuhamelTailSecondMomentUniformEnvelope ν A (a / 2) t := by
    unfold h3SelectedDuhamelTailSecondMomentUniformEnvelope
    exact
      add_le_add
        (add_le_add hTailHead hVariation)
        hFrozenRefl

  unfold h3SelectedMildSecondMomentUniformEnvelope

  exact
    add_le_add
      (add_le_add hFree hHead)
      hTail

/-- The uniform selected quarter forcing envelope respects the same nested half
intervals. -/
theorem h3SelectedForcingQuarterMomentUniformEnvelope_halfInterval_le
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedForcingQuarterMomentUniformEnvelope ν A (r / 2) r
      ≤
    h3SelectedForcingQuarterMomentUniformEnvelope ν A (a / 2) t := by
  let M2r : ℝ :=
    h3SelectedMildSecondMomentUniformEnvelope ν A (r / 2) r
  let M2u : ℝ :=
    h3SelectedMildSecondMomentUniformEnvelope ν A (a / 2) t
  let M0 : ℝ :=
    h3SelectedRestartRawFourierL1Envelope A

  have hM2 : M2r ≤ M2u := by
    dsimp only [M2r, M2u]
    exact
      h3SelectedMildSecondMomentUniformEnvelope_halfInterval_le
        hν hA ha har hrt

  have hM0 : 0 ≤ M0 := by
    dsimp only [M0]
    exact h3SelectedRestartRawFourierL1Envelope_nonneg hA

  have hLeft :
      M2r * M0 ≤ M2u * M0 :=
    mul_le_mul_of_nonneg_right hM2 hM0

  have hRight :
      M0 * M2r ≤ M0 * M2u :=
    mul_le_mul_of_nonneg_left hM2 hM0

  have hPair :
      M2r * M0 + M0 * M2r
        ≤
      M2u * M0 + M0 * M2u :=
    add_le_add hLeft hRight

  have hTwo :
      2 * (M2r * M0 + M0 * M2r)
        ≤
      2 * (M2u * M0 + M0 * M2u) :=
    mul_le_mul_of_nonneg_left hPair (by norm_num)

  have hFirstTerm :
      ∀ k j : Fin 3,
        (2 * Real.pi) *
            (2 * (M2r * M0 + M0 * M2r))
          ≤
        (2 * Real.pi) *
            (2 * (M2u * M0 + M0 * M2u)) := by
    intro _k _j
    exact mul_le_mul_of_nonneg_left hTwo (by positivity)

  have hFirstSum :
      (∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (2 * (M2r * M0 + M0 * M2r)))
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (2 * (M2u * M0 + M0 * M2u)) :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun j _ =>
        hFirstTerm k j

  have hFirst :
      h3SelectedForcingFirstMomentUniformEnvelope ν A (r / 2) r
        ≤
      h3SelectedForcingFirstMomentUniformEnvelope ν A (a / 2) t := by
    unfold h3SelectedForcingFirstMomentUniformEnvelope
    dsimp only [M2r, M2u, M0] at hFirstSum ⊢
    exact
      mul_le_mul_of_nonneg_left hFirstSum (by norm_num)

  have hL1Inside :
      M0 * M0 + 2 * (M2r * M0 + M0 * M2r)
        ≤
      M0 * M0 + 2 * (M2u * M0 + M0 * M2u) :=
    add_le_add (le_refl _) hTwo

  have hL1Term :
      ∀ k j : Fin 3,
        (2 * Real.pi) *
            (M0 * M0 + 2 * (M2r * M0 + M0 * M2r))
          ≤
        (2 * Real.pi) *
            (M0 * M0 + 2 * (M2u * M0 + M0 * M2u)) := by
    intro _k _j
    exact
      mul_le_mul_of_nonneg_left hL1Inside (by positivity)

  have hL1Sum :
      (∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (M0 * M0 + 2 * (M2r * M0 + M0 * M2r)))
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (M0 * M0 + 2 * (M2u * M0 + M0 * M2u)) :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun j _ =>
        hL1Term k j

  have hL1 :
      h3SelectedForcingL1UniformEnvelope ν A (r / 2) r
        ≤
      h3SelectedForcingL1UniformEnvelope ν A (a / 2) t := by
    unfold h3SelectedForcingL1UniformEnvelope
    dsimp only [M2r, M2u, M0] at hL1Sum ⊢
    exact
      mul_le_mul_of_nonneg_left hL1Sum (by norm_num)

  unfold h3SelectedForcingQuarterMomentUniformEnvelope
  exact add_le_add hL1 hFirst

/-- The uniform selected `9/4` state envelope respects nested half intervals. -/
theorem h3SelectedMildNineQuarterMomentUniformEnvelope_halfInterval_le
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedMildNineQuarterMomentUniformEnvelope ν A (r / 2) r
      ≤
    h3SelectedMildNineQuarterMomentUniformEnvelope ν A (a / 2) t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har
  have ht : 0 < t :=
    lt_of_lt_of_le hr hrt

  have ha2 : 0 < a / 2 := by positivity
  have ha4 : 0 < a / 2 / 2 := by positivity

  have hBase2 : a / 2 ≤ r / 2 := by linarith
  have hBase4 : a / 2 / 2 ≤ r / 2 / 2 := by linarith

  have hFreeHeat :
      h3HeatNineQuarterMomentCoefficient ν (r / 2)
        ≤
      h3HeatNineQuarterMomentCoefficient ν (a / 2) :=
    h3HeatNineQuarterMomentCoefficient_antitone_pos
      hν ha2 hBase2

  have hHeadHeat :
      h3HeatNineQuarterMomentCoefficient ν (r / 2 / 2)
        ≤
      h3HeatNineQuarterMomentCoefficient ν (a / 2 / 2) :=
    h3HeatNineQuarterMomentCoefficient_antitone_pos
      hν ha4 hBase4

  have hCdw0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient :=
    h3RawFourierL1DeweightingCoefficient_nonneg

  have hFreeFactor0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient * A :=
    mul_nonneg hCdw0 hA

  have hFree :
      h3HeatNineQuarterMomentCoefficient ν (r / 2) *
          h3RawFourierL1DeweightingCoefficient * A
        ≤
      h3HeatNineQuarterMomentCoefficient ν (a / 2) *
          h3RawFourierL1DeweightingCoefficient * A := by
    calc
      h3HeatNineQuarterMomentCoefficient ν (r / 2) *
            h3RawFourierL1DeweightingCoefficient * A
          =
        h3HeatNineQuarterMomentCoefficient ν (r / 2) *
          (h3RawFourierL1DeweightingCoefficient * A) := by ring
      _ ≤
        h3HeatNineQuarterMomentCoefficient ν (a / 2) *
          (h3RawFourierL1DeweightingCoefficient * A) :=
        mul_le_mul_of_nonneg_right hFreeHeat hFreeFactor0
      _ =
        h3HeatNineQuarterMomentCoefficient ν (a / 2) *
          h3RawFourierL1DeweightingCoefficient * A := by ring

  have hH3 :
      h3SelectedDuhamelHalfTimeH3Envelope ν A r
        ≤
      h3SelectedDuhamelHalfTimeH3Envelope ν A t :=
    h3SelectedDuhamelHalfTimeH3Envelope_mono
      hA hr.le hrt

  have hH3r0 :
      0 ≤ h3SelectedDuhamelHalfTimeH3Envelope ν A r :=
    h3SelectedDuhamelHalfTimeH3Envelope_nonneg hA

  have hHeadUpper0 :
      0 ≤ h3HeatNineQuarterMomentCoefficient ν (a / 2 / 2) :=
    h3HeatNineQuarterMomentCoefficient_nonneg hν.le (by positivity)

  have hHead :
      h3HeatNineQuarterMomentCoefficient ν (r / 2 / 2) *
          h3RawFourierL1DeweightingCoefficient *
          h3SelectedDuhamelHalfTimeH3Envelope ν A r
        ≤
      h3HeatNineQuarterMomentCoefficient ν (a / 2 / 2) *
          h3RawFourierL1DeweightingCoefficient *
          h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
    calc
      h3HeatNineQuarterMomentCoefficient ν (r / 2 / 2) *
            h3RawFourierL1DeweightingCoefficient *
            h3SelectedDuhamelHalfTimeH3Envelope ν A r
          ≤
        h3HeatNineQuarterMomentCoefficient ν (a / 2 / 2) *
            h3RawFourierL1DeweightingCoefficient *
            h3SelectedDuhamelHalfTimeH3Envelope ν A r :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hHeadHeat hCdw0)
          hH3r0
      _ ≤
        h3HeatNineQuarterMomentCoefficient ν (a / 2 / 2) *
            h3RawFourierL1DeweightingCoefficient *
            h3SelectedDuhamelHalfTimeH3Envelope ν A t :=
        mul_le_mul_of_nonneg_left
          hH3
          (mul_nonneg hHeadUpper0 hCdw0)

  let Kr : ℝ :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
      ν A (r / 2 / 2) r
  let Ku : ℝ :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
      ν A (a / 2 / 2) t
  let Cr : ℝ :=
    h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient ν Kr
  let Cu : ℝ :=
    h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient ν Ku

  have hK : Kr ≤ Ku := by
    dsimp only [Kr, Ku]
    exact
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_interval_mono
        hν hA ha4 hBase4 hr.le hrt

  have hC : Cr ≤ Cu := by
    dsimp only [Cr, Cu]
    exact
      h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient_mono
        hν hK

  have hKr0 : 0 ≤ Kr := by
    dsimp only [Kr]
    exact
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_nonneg
        hν.le hA hr.le

  have hKu0 : 0 ≤ Ku := by
    dsimp only [Ku]
    exact
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_nonneg
        hν.le hA ht.le

  have hCr0 : 0 ≤ Cr := by
    dsimp only [Cr]
    unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
    exact
      mul_nonneg
        (Real.rpow_nonneg (by positivity) _)
        hKr0

  have hCu0 : 0 ≤ Cu := by
    dsimp only [Cu]
    unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
    exact
      mul_nonneg
        (Real.rpow_nonneg (by positivity) _)
        hKu0

  have hLag0 : 0 ≤ r - r / 2 := by linarith
  have hLag : r - r / 2 ≤ t - t / 2 := by linarith

  have hPow :
      (r - r / 2) ^ ((1 : ℝ) / 8)
        ≤
      (t - t / 2) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow hLag0 hLag (by norm_num)

  have hPow0 :
      0 ≤ (r - r / 2) ^ ((1 : ℝ) / 8) :=
    Real.rpow_nonneg hLag0 _

  have hVar :
      8 * Cr * (r - r / 2) ^ ((1 : ℝ) / 8)
        ≤
      8 * Cu * (t - t / 2) ^ ((1 : ℝ) / 8) := by
    have hEight : 8 * Cr ≤ 8 * Cu :=
      mul_le_mul_of_nonneg_left hC (by norm_num)
    have hEightCu0 : 0 ≤ 8 * Cu :=
      mul_nonneg (by norm_num) hCu0
    calc
      8 * Cr * (r - r / 2) ^ ((1 : ℝ) / 8)
          ≤
        8 * Cu * (r - r / 2) ^ ((1 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_right hEight hPow0
      _ ≤
        8 * Cu * (t - t / 2) ^ ((1 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left hPow hEightCu0

  have hQuarter :=
    h3SelectedForcingQuarterMomentUniformEnvelope_halfInterval_le
      hν hA ha har hrt

  have hc0 :
      0 ≤ (((2 * Real.pi) ^ 2 * ν)⁻¹) := by
    positivity

  have hFrozen :
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
          h3SelectedForcingQuarterMomentUniformEnvelope ν A (r / 2) r
        ≤
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
          h3SelectedForcingQuarterMomentUniformEnvelope ν A (a / 2) t :=
    mul_le_mul_of_nonneg_left hQuarter hc0

  unfold
    h3SelectedMildNineQuarterMomentUniformEnvelope
    h3SelectedDuhamelNineQuarterMomentUniformEnvelope
    h3SelectedDuhamelHeadNineQuarterMomentUniformEnvelope
    h3SelectedDuhamelTailNineQuarterUniformEnvelope
    h3SelectedDuhamelTailNineQuarterVariationUniformEnvelope
    h3SelectedDuhamelTailNineQuarterFrozenUniformEnvelope

  dsimp only [Kr, Ku, Cr, Cu] at hVar

  exact
    add_le_add
      hFree
      (add_le_add
        hHead
        (add_le_add hVar hFrozen))

/-- The diagonal `5/4` forcing envelope is monotone in its nonnegative
`9/4` state argument when the unweighted state envelope is fixed. -/
theorem h3FiveQuarterForcingDiagonalEnvelope_mono_right
    {M0 M9₁ M9₂ : ℝ}
    (hM0 : 0 ≤ M0)
    (_hM9₁ : 0 ≤ M9₁)
    (hM9 : M9₁ ≤ M9₂) :
    h3FiveQuarterForcingDiagonalEnvelope M0 M9₁
      ≤
    h3FiveQuarterForcingDiagonalEnvelope M0 M9₂ := by
  have hLeft :
      M9₁ * M0 ≤ M9₂ * M0 :=
    mul_le_mul_of_nonneg_right hM9 hM0

  have hRight :
      M0 * M9₁ ≤ M0 * M9₂ :=
    mul_le_mul_of_nonneg_left hM9 hM0

  have hPair :
      M9₁ * M0 + M0 * M9₁
        ≤
      M9₂ * M0 + M0 * M9₂ :=
    add_le_add hLeft hRight

  have hSplit0 :
      0 ≤ h3FourierNineQuarterSplitCoefficient := by
    unfold h3FourierNineQuarterSplitCoefficient
    exact Real.rpow_nonneg (by norm_num) _

  have hInner :
      h3FourierNineQuarterSplitCoefficient *
          (M9₁ * M0 + M0 * M9₁)
        ≤
      h3FourierNineQuarterSplitCoefficient *
          (M9₂ * M0 + M0 * M9₂) :=
    mul_le_mul_of_nonneg_left hPair hSplit0

  have hTerm :
      ∀ k j : Fin 3,
        (2 * Real.pi) *
            (h3FourierNineQuarterSplitCoefficient *
              (M9₁ * M0 + M0 * M9₁))
          ≤
        (2 * Real.pi) *
            (h3FourierNineQuarterSplitCoefficient *
              (M9₂ * M0 + M0 * M9₂)) := by
    intro _k _j
    exact
      mul_le_mul_of_nonneg_left hInner (by positivity)

  have hSum :
      (∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3FourierNineQuarterSplitCoefficient *
                (M9₁ * M0 + M0 * M9₁)))
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierNineQuarterSplitCoefficient *
              (M9₂ * M0 + M0 * M9₂)) :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun j _ =>
        hTerm k j

  unfold
    h3FiveQuarterForcingDiagonalEnvelope
    h3FiveQuarterForcingBilinearEnvelope

  exact
    mul_le_mul_of_nonneg_left hSum (by norm_num)

/-- Uniform full-third variation-tail budget on `[a,t]`. -/
noncomputable def h3SelectedDuhamelTailThirdVariationIntervalUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3SelectedForcingDifferenceFiveQuarterUniformEnvelope
      ν A (a / 2) t *
    (8 *
      h3HeatSevenQuarterNormalizedCoefficient ν *
      (t - t / 2) ^ ((1 : ℝ) / 8))

/-- Uniform frozen third-tail budget on `[a,t]`. -/
noncomputable def h3SelectedDuhamelTailThirdFrozenIntervalUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  (((2 * Real.pi) ^ 2 * ν)⁻¹) *
    h3SelectedForcingFirstMomentUniformEnvelope ν A a t

/-- Uniform complete third terminal-tail budget on `[a,t]`. -/
noncomputable def h3SelectedDuhamelTailThirdIntervalUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3SelectedDuhamelTailThirdVariationIntervalUniformEnvelope ν A a t +
    h3SelectedDuhamelTailThirdFrozenIntervalUniformEnvelope ν A a t

/-- Uniform midpoint-head cubic budget on `[a,t]`. -/
noncomputable def h3SelectedDuhamelHeadThirdMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3HeatThirdMomentRawL1Coefficient ν (a / 2) *
    h3RawFourierL1DeweightingCoefficient *
    h3SelectedDuhamelHalfTimeH3Envelope ν A t

/-- Uniform complete selected Duhamel cubic budget on `[a,t]`. -/
noncomputable def h3SelectedDuhamelThirdMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3SelectedDuhamelHeadThirdMomentUniformEnvelope ν A a t +
    h3SelectedDuhamelTailThirdIntervalUniformEnvelope ν A a t

/-- Uniform selected mild-state cubic budget on `[a,t]`. -/
noncomputable def h3SelectedMildThirdMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3HeatThirdMomentRawL1Coefficient ν a *
      h3RawFourierL1DeweightingCoefficient * A
    +
  h3SelectedDuhamelThirdMomentUniformEnvelope ν A a t

/-- The pointwise selected full-third variation budget is dominated by the
interval-uniform variation budget. -/
theorem h3SelectedDuhamelTailThirdVariationUniformBudget_le_intervalUniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    h3SelectedDuhamelTailThirdVariationUniformBudget ν A (r / 2) r
      ≤
    h3SelectedDuhamelTailThirdVariationIntervalUniformEnvelope ν A a t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hr2 : 0 < r / 2 := by positivity
  have ha2 : 0 < a / 2 := by positivity
  have hrHalf : r / 2 < r := by linarith
  have haHalfT : a / 2 < t := by
    linarith

  let M0 : ℝ :=
    h3SelectedRestartRawFourierL1Envelope A

  let M9r : ℝ :=
    h3SelectedMildNineQuarterMomentUniformEnvelope ν A (r / 2) r

  let M9u : ℝ :=
    h3SelectedMildNineQuarterMomentUniformEnvelope ν A (a / 2) t

  have hM0 : 0 ≤ M0 := by
    dsimp only [M0]
    exact h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM9r0 : 0 ≤ M9r := by
    dsimp only [M9r]
    have hrR : r ≤ h3FinHeatLerayRestartRadius ν A :=
      le_trans hrt htR
    exact
      h3SelectedMildNineQuarterMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ hr2 hrHalf hrR

  have hM9 :
      M9r ≤ M9u := by
    dsimp only [M9r, M9u]
    exact
      h3SelectedMildNineQuarterMomentUniformEnvelope_halfInterval_le
        hν hA.le ha har hrt

  have hDiag :
      h3FiveQuarterForcingDiagonalEnvelope M0 M9r
        ≤
      h3FiveQuarterForcingDiagonalEnvelope M0 M9u :=
    h3FiveQuarterForcingDiagonalEnvelope_mono_right
      hM0 hM9r0 hM9

  have hB :
      h3SelectedForcingDifferenceFiveQuarterUniformEnvelope
          ν A (r / 2) r
        ≤
      h3SelectedForcingDifferenceFiveQuarterUniformEnvelope
          ν A (a / 2) t := by
    unfold h3SelectedForcingDifferenceFiveQuarterUniformEnvelope
    dsimp only [M0, M9r, M9u] at hDiag ⊢
    exact
      mul_le_mul_of_nonneg_left hDiag (by norm_num)

  have hBu0 :
      0 ≤
        h3SelectedForcingDifferenceFiveQuarterUniformEnvelope
          ν A (a / 2) t := by
    exact
      h3SelectedForcingDifferenceFiveQuarterUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha2 haHalfT htR

  have hLag0 : 0 ≤ r - r / 2 := by linarith
  have hLag : r - r / 2 ≤ t - t / 2 := by linarith

  have hPow :
      (r - r / 2) ^ ((1 : ℝ) / 8)
        ≤
      (t - t / 2) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow hLag0 hLag (by norm_num)

  have hScale0 :
      0 ≤ 8 * h3HeatSevenQuarterNormalizedCoefficient ν := by
    unfold h3HeatSevenQuarterNormalizedCoefficient
    positivity

  have hOldPow0 :
      0 ≤
        8 * h3HeatSevenQuarterNormalizedCoefficient ν *
          (r - r / 2) ^ ((1 : ℝ) / 8) :=
    mul_nonneg
      hScale0
      (Real.rpow_nonneg hLag0 _)

  have hNewPow :
      8 * h3HeatSevenQuarterNormalizedCoefficient ν *
          (r - r / 2) ^ ((1 : ℝ) / 8)
        ≤
      8 * h3HeatSevenQuarterNormalizedCoefficient ν *
          (t - t / 2) ^ ((1 : ℝ) / 8) :=
    mul_le_mul_of_nonneg_left hPow hScale0

  unfold
    h3SelectedDuhamelTailThirdVariationUniformBudget
    h3SelectedDuhamelTailThirdVariationBudget
    h3SelectedDuhamelTailThirdVariationIntervalUniformEnvelope

  calc
    h3SelectedForcingDifferenceFiveQuarterUniformEnvelope
          ν A (r / 2) r *
        (8 *
          h3HeatSevenQuarterNormalizedCoefficient ν *
          (r - r / 2) ^ ((1 : ℝ) / 8))
        ≤
      h3SelectedForcingDifferenceFiveQuarterUniformEnvelope
          ν A (a / 2) t *
        (8 *
          h3HeatSevenQuarterNormalizedCoefficient ν *
          (r - r / 2) ^ ((1 : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_right hB hOldPow0
    _ ≤
      h3SelectedForcingDifferenceFiveQuarterUniformEnvelope
          ν A (a / 2) t *
        (8 *
          h3HeatSevenQuarterNormalizedCoefficient ν *
          (t - t / 2) ^ ((1 : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_left hNewPow hBu0

/-- The pointwise frozen cubic tail budget is dominated by the uniform first
forcing envelope. -/
theorem h3SelectedDuhamelTailThirdFrozenBudget_le_intervalUniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedDuhamelTailThirdFrozenBudget ν A r
      ≤
    h3SelectedDuhamelTailThirdFrozenIntervalUniformEnvelope ν A a t := by
  have hFirst :=
    h3SelectedForcingFirstMomentEnvelope_le_uniform_on
      hν hA ha har hrt

  have hc0 :
      0 ≤ (((2 * Real.pi) ^ 2 * ν)⁻¹) := by
    positivity

  unfold
    h3SelectedDuhamelTailThirdFrozenBudget
    h3SelectedDuhamelTailThirdFrozenIntervalUniformEnvelope

  exact
    mul_le_mul_of_nonneg_left hFirst hc0

/-- The complete pointwise selected terminal-tail cubic budget is dominated by
one interval-uniform tail budget. -/
theorem h3SelectedDuhamelTailThirdFullBudget_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    h3SelectedDuhamelTailThirdFullBudget ν A r
      ≤
    h3SelectedDuhamelTailThirdIntervalUniformEnvelope ν A a t := by
  unfold
    h3SelectedDuhamelTailThirdFullBudget
    h3SelectedDuhamelTailThirdIntervalUniformEnvelope

  exact
    add_le_add
      (h3SelectedDuhamelTailThirdVariationUniformBudget_le_intervalUniform_on
        hν U₀ hA hU₀ ha har hrt htR)
      (h3SelectedDuhamelTailThirdFrozenBudget_le_intervalUniform_on
        hν hA.le ha har hrt)

/-- The pointwise selected Duhamel cubic envelope is dominated by one
interval-uniform Duhamel envelope. -/
theorem h3SelectedDuhamelThirdMomentEnvelope_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    h3SelectedDuhamelThirdMomentEnvelope ν A r
      ≤
    h3SelectedDuhamelThirdMomentUniformEnvelope ν A a t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have haHalf : 0 < a / 2 := by positivity
  have hHalf : a / 2 ≤ r / 2 := by linarith

  have hHeat :
      h3HeatThirdMomentRawL1Coefficient ν (r / 2)
        ≤
      h3HeatThirdMomentRawL1Coefficient ν (a / 2) :=
    h3HeatThirdMomentRawL1Coefficient_antitone_pos
      hν haHalf hHalf

  have hH3 :
      h3SelectedDuhamelHalfTimeH3Envelope ν A r
        ≤
      h3SelectedDuhamelHalfTimeH3Envelope ν A t :=
    h3SelectedDuhamelHalfTimeH3Envelope_mono
      hA.le hr.le hrt

  have hCdw0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient :=
    h3RawFourierL1DeweightingCoefficient_nonneg

  have hH3r0 :
      0 ≤ h3SelectedDuhamelHalfTimeH3Envelope ν A r :=
    h3SelectedDuhamelHalfTimeH3Envelope_nonneg hA.le

  have hHeatUpper0 :
      0 ≤ h3HeatThirdMomentRawL1Coefficient ν (a / 2) :=
    h3HeatThirdMomentRawL1Coefficient_nonneg _ _

  have hHead :
      h3SelectedDuhamelHeadThirdMomentEnvelope ν A r
        ≤
      h3SelectedDuhamelHeadThirdMomentUniformEnvelope ν A a t := by
    unfold
      h3SelectedDuhamelHeadThirdMomentEnvelope
      h3SelectedDuhamelHeadThirdMomentUniformEnvelope

    calc
      h3HeatThirdMomentRawL1Coefficient ν (r / 2) *
            h3RawFourierL1DeweightingCoefficient *
            h3SelectedDuhamelHalfTimeH3Envelope ν A r
          ≤
        h3HeatThirdMomentRawL1Coefficient ν (a / 2) *
            h3RawFourierL1DeweightingCoefficient *
            h3SelectedDuhamelHalfTimeH3Envelope ν A r :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hHeat hCdw0)
          hH3r0
      _ ≤
        h3HeatThirdMomentRawL1Coefficient ν (a / 2) *
            h3RawFourierL1DeweightingCoefficient *
            h3SelectedDuhamelHalfTimeH3Envelope ν A t :=
        mul_le_mul_of_nonneg_left
          hH3
          (mul_nonneg hHeatUpper0 hCdw0)

  have hTail :=
    h3SelectedDuhamelTailThirdFullBudget_le_uniform_on
      hν U₀ hA hU₀ ha har hrt htR

  unfold
    h3SelectedDuhamelThirdMomentEnvelope
    h3SelectedDuhamelThirdMomentUniformEnvelope

  exact add_le_add hHead hTail

/-- The pointwise selected mild cubic envelope is dominated by one interval
constant. -/
theorem h3SelectedMildThirdMomentEnvelope_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    h3SelectedMildThirdMomentEnvelope ν A r
      ≤
    h3SelectedMildThirdMomentUniformEnvelope ν A a t := by
  have hHeat :
      h3HeatThirdMomentRawL1Coefficient ν r
        ≤
      h3HeatThirdMomentRawL1Coefficient ν a :=
    h3HeatThirdMomentRawL1Coefficient_antitone_pos
      hν ha har

  have hFactor0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient * A :=
    mul_nonneg
      h3RawFourierL1DeweightingCoefficient_nonneg
      hA.le

  have hFree :
      h3HeatThirdMomentRawL1Coefficient ν r *
          h3RawFourierL1DeweightingCoefficient * A
        ≤
      h3HeatThirdMomentRawL1Coefficient ν a *
          h3RawFourierL1DeweightingCoefficient * A := by
    calc
      h3HeatThirdMomentRawL1Coefficient ν r *
            h3RawFourierL1DeweightingCoefficient * A
          =
        h3HeatThirdMomentRawL1Coefficient ν r *
          (h3RawFourierL1DeweightingCoefficient * A) := by ring
      _ ≤
        h3HeatThirdMomentRawL1Coefficient ν a *
          (h3RawFourierL1DeweightingCoefficient * A) :=
        mul_le_mul_of_nonneg_right hHeat hFactor0
      _ =
        h3HeatThirdMomentRawL1Coefficient ν a *
          h3RawFourierL1DeweightingCoefficient * A := by ring

  have hDuhamel :=
    h3SelectedDuhamelThirdMomentEnvelope_le_uniform_on
      hν U₀ hA hU₀ ha har hrt htR

  unfold
    h3SelectedMildThirdMomentEnvelope
    h3SelectedMildThirdMomentUniformEnvelope

  exact add_le_add hFree hDuhamel

/-- Every selected mild coordinate has one canonical cubic raw Fourier mass
bound valid throughout `[a,t]`. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMass_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralScalarRawFourierThirdMass
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ r i)
      ≤
    h3SelectedMildThirdMomentUniformEnvelope ν A a t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have hPoint :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMass_le
      hν U₀ hA hU₀ hr hrR i

  exact
    le_trans hPoint
      (h3SelectedMildThirdMomentEnvelope_le_uniform_on
        hν U₀ hA hU₀ ha har hrt htR)

/-- The new uniform cubic state envelope is nonnegative on every nonempty
positive interval. -/
theorem h3SelectedMildThirdMomentUniformEnvelope_nonneg
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    0 ≤ h3SelectedMildThirdMomentUniformEnvelope ν A a t := by
  let k0 : Fin 3 := 0

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hMass0 :
      0 ≤ h3SpectralScalarRawFourierThirdMass (W a k0) :=
    h3SpectralScalarRawFourierThirdMass_nonneg (W a k0)

  have hBound0 :
      h3SpectralScalarRawFourierThirdMass (W a k0)
        ≤
      h3SelectedMildThirdMomentUniformEnvelope ν A a t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMass_le_uniform_on
        hν U₀ hA hU₀ ha (le_refl a) hat.le htR k0

  exact le_trans hMass0 hBound0

end
end Euclidean
end Bridge
end PrimeTensor
