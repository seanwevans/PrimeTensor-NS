import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentSlab

/-!
# Fréchet endpoint induction: the uniform intermediate slab

A pointwise moment is not the right induction invariant for a Duhamel tail:
the terminal half at time `r` samples source times in `(r/2,r)`.  Therefore
the first bootstrap half-step has the interval geometry

    M_n on [a/2,t]
      ->
    N_{n-1} on every terminal source interval
      ->
    M_{n+3/4} on [a,t].

This file proves that implication with explicit uniform budgets.

The only time-uniform heat fact needed is elementary semigroup monotonicity:
if a weighted heat multiplier is bounded at one positive lag `τ`, then the
same bound remains valid at every later lag.  We use that twice:

* the midpoint head uses the fixed residual `3/4` heat bound at lag `a/2`;
* the free heat uses the fixed all-orders `n+3/4` bound at lag `a`.

The terminal tail is bounded by enlarging `(r/2,r)` to the single containing
positive interval `(a/2,t)`, exactly as in the earlier concrete uniform-tail
constructions.

No named Fourier endpoint occurs in the theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentIntermediateSlab
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-!
## Heat bounds persist to later positive times
-/

/-- A radial weighted heat multiplier bound at one positive lag persists at
every later lag by the heat semigroup law and the contractive bound
`‖H_σ‖ ≤ 1`. -/
theorem h3HeatFourierSymbol_momentBound_of_le_time
    {p ν τ r C : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (hτr : τ ≤ r)
    (hC0 : 0 ≤ C)
    (hBound :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖
          ≤
        C)
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight p ξ *
        ‖h3HeatFourierSymbol ν r ξ‖
      ≤
    C := by
  have hLater : 0 ≤ r - τ :=
    sub_nonneg.mpr hτr

  have hSplit :
      ‖h3HeatFourierSymbol ν r ξ‖
        =
      ‖h3HeatFourierSymbol ν τ ξ‖ *
        ‖h3HeatFourierSymbol ν (r - τ) ξ‖ := by
    have hr :
        τ + (r - τ) = r := by
      ring
    calc
      ‖h3HeatFourierSymbol ν r ξ‖
          =
        ‖h3HeatFourierSymbol ν (τ + (r - τ)) ξ‖ := by
          rw [hr]
      _ =
        ‖h3HeatFourierSymbol ν (r - τ) ξ *
          h3HeatFourierSymbol ν τ ξ‖ := by
          rw [h3HeatFourierSymbol_add]
      _ =
        ‖h3HeatFourierSymbol ν τ ξ *
          h3HeatFourierSymbol ν (r - τ) ξ‖ := by
          rw [mul_comm]
      _ =
        ‖h3HeatFourierSymbol ν τ ξ‖ *
          ‖h3HeatFourierSymbol ν (r - τ) ξ‖ := by
          rw [norm_mul]

  have hContract :
      ‖h3HeatFourierSymbol ν (r - τ) ξ‖ ≤ 1 :=
    norm_h3HeatFourierSymbol_le_one
      hν.le hLater ξ

  rw [hSplit]

  calc
    h3FourierMomentWeight p ξ *
        (‖h3HeatFourierSymbol ν τ ξ‖ *
          ‖h3HeatFourierSymbol ν (r - τ) ξ‖)
        =
      (h3FourierMomentWeight p ξ *
        ‖h3HeatFourierSymbol ν τ ξ‖) *
        ‖h3HeatFourierSymbol ν (r - τ) ξ‖ := by
      ring
    _ ≤
      C * ‖h3HeatFourierSymbol ν (r - τ) ξ‖ :=
      mul_le_mul_of_nonneg_right
        (hBound ξ)
        (norm_nonneg _)
    _ ≤
      C * 1 :=
      mul_le_mul_of_nonneg_left
        hContract hC0
    _ = C := by
      ring

/-!
## Uniform intermediate budgets
-/

/-- One slab-wide forcing constant generated from the incoming natural
`n`-moment slab. -/
noncomputable def h3SelectedIntermediateSlabForcingBudget
    (n : ℕ)
    (BState B0 : ℝ) : ℝ :=
  h3SelectedMomentSlabForcingEnvelope
    (n : ℝ) BState B0

/-- The midpoint-head budget for the intermediate `n+3/4` Duhamel moment. -/
noncomputable def h3SelectedIntermediateSlabHeadBudget
    (ν a BDuhamel : ℝ) : ℝ :=
  h3HeatThreeQuarterMomentCoefficient ν (a / 2) *
    BDuhamel

/-- One enlarged terminal-tail budget valid for every output time
`r ∈ [a,t]`. -/
noncomputable def h3SelectedIntermediateSlabTailBudget
    (n : ℕ)
    (ν a t BState B0 : ℝ) : ℝ :=
  h3SelectedDuhamelSevenQuarterSourceBudget
    ν (a / 2) t
    (h3SelectedIntermediateSlabForcingBudget
      n BState B0)

/-- Uniform complete-Duhamel budget at the intermediate exponent. -/
noncomputable def h3SelectedIntermediateSlabDuhamelBudget
    (n : ℕ)
    (ν a t BState BDuhamel B0 : ℝ) : ℝ :=
  h3SelectedIntermediateSlabHeadBudget ν a BDuhamel +
    h3SelectedIntermediateSlabTailBudget
      n ν a t BState B0

/-- Uniform free-heat budget at exponent `n+3/4`, evaluated at the smallest
output heat time `a`. -/
noncomputable def h3SelectedIntermediateSlabHeatBudget
    (n : ℕ)
    (ν A a : ℝ) : ℝ :=
  h3HeatNatAddThreeQuarterMomentCoefficient n ν a *
    h3RawFourierL1DeweightingCoefficient *
    A

/-- Uniform mild-state budget at the intermediate exponent. -/
noncomputable def h3SelectedIntermediateSlabStateBudget
    (n : ℕ)
    (ν A a t BState BDuhamel B0 : ℝ) : ℝ :=
  h3SelectedIntermediateSlabHeatBudget n ν A a +
    h3SelectedIntermediateSlabDuhamelBudget
      n ν a t BState BDuhamel B0

theorem h3SelectedIntermediateSlabForcingBudget_nonneg
    {n : ℕ}
    {BState B0 : ℝ}
    (hBS : 0 ≤ BState)
    (hB0 : 0 ≤ B0) :
    0 ≤
      h3SelectedIntermediateSlabForcingBudget
        n BState B0 := by
  unfold h3SelectedIntermediateSlabForcingBudget
  exact
    h3SelectedMomentSlabForcingEnvelope_nonneg
      hBS hB0

theorem h3SelectedIntermediateSlabHeadBudget_nonneg
    {ν a BDuhamel : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hBD : 0 ≤ BDuhamel) :
    0 ≤
      h3SelectedIntermediateSlabHeadBudget
        ν a BDuhamel := by
  unfold h3SelectedIntermediateSlabHeadBudget
  exact
    mul_nonneg
      (h3HeatThreeQuarterMomentCoefficient_nonneg
        hν.le (by positivity))
      hBD

theorem h3SelectedIntermediateSlabTailBudget_nonneg
    {n : ℕ}
    {ν a t BState B0 : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hat : a ≤ t)
    (hBS : 0 ≤ BState)
    (hB0 : 0 ≤ B0) :
    0 ≤
      h3SelectedIntermediateSlabTailBudget
        n ν a t BState B0 := by
  have hForce0 :
      0 ≤
        h3SelectedIntermediateSlabForcingBudget
          n BState B0 :=
    h3SelectedIntermediateSlabForcingBudget_nonneg
      hBS hB0

  have hLag0 :
      0 ≤ t - a / 2 := by
    linarith

  unfold
    h3SelectedIntermediateSlabTailBudget
    h3SelectedDuhamelSevenQuarterSourceBudget

  have hScale0 :
      0 ≤
        8 *
          h3HeatSevenQuarterNormalizedCoefficient ν *
          (t - a / 2) ^ ((1 : ℝ) / 8) := by
    unfold h3HeatSevenQuarterNormalizedCoefficient
    positivity

  exact mul_nonneg hForce0 hScale0

theorem h3SelectedIntermediateSlabDuhamelBudget_nonneg
    {n : ℕ}
    {ν a t BState BDuhamel B0 : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hat : a ≤ t)
    (hBS : 0 ≤ BState)
    (hBD : 0 ≤ BDuhamel)
    (hB0 : 0 ≤ B0) :
    0 ≤
      h3SelectedIntermediateSlabDuhamelBudget
        n ν a t BState BDuhamel B0 := by
  unfold h3SelectedIntermediateSlabDuhamelBudget
  exact
    add_nonneg
      (h3SelectedIntermediateSlabHeadBudget_nonneg
        hν ha hBD)
      (h3SelectedIntermediateSlabTailBudget_nonneg
        hν ha hat hBS hB0)

theorem h3SelectedIntermediateSlabHeatBudget_nonneg
    (n : ℕ)
    {ν A a : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hA : 0 < A) :
    0 ≤
      h3SelectedIntermediateSlabHeatBudget
        n ν A a := by
  unfold h3SelectedIntermediateSlabHeatBudget
  exact
    mul_nonneg
      (mul_nonneg
        (h3HeatNatAddThreeQuarterMomentCoefficient_nonneg
          n hν.le ha.le)
        h3RawFourierL1DeweightingCoefficient_nonneg)
      hA.le

theorem h3SelectedIntermediateSlabStateBudget_nonneg
    {n : ℕ}
    {ν A a t BState BDuhamel B0 : ℝ}
    (hν : 0 < ν)
    (hA : 0 < A)
    (ha : 0 < a)
    (hat : a ≤ t)
    (hBS : 0 ≤ BState)
    (hBD : 0 ≤ BDuhamel)
    (hB0 : 0 ≤ B0) :
    0 ≤
      h3SelectedIntermediateSlabStateBudget
        n ν A a t BState BDuhamel B0 := by
  unfold h3SelectedIntermediateSlabStateBudget
  exact
    add_nonneg
      (h3SelectedIntermediateSlabHeatBudget_nonneg
        n hν ha hA)
      (h3SelectedIntermediateSlabDuhamelBudget_nonneg
        hν ha hat hBS hBD hB0)

/-!
## Local terminal-tail budget versus the one global slab budget
-/

/-- Every local terminal-half source budget occurring at
`r ∈ [a,t]` is bounded by the one enlarged source budget on `(a/2,t)`. -/
theorem h3SelectedDuhamelSevenQuarterSourceBudget_local_le_intermediateSlab
    {n : ℕ}
    {ν a r t BState B0 : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (hBS : 0 ≤ BState)
    (hB0 : 0 ≤ B0) :
    h3SelectedDuhamelSevenQuarterSourceBudget
        ν (r / 2) r
        (h3SelectedIntermediateSlabForcingBudget
          n BState B0)
      ≤
    h3SelectedIntermediateSlabTailBudget
      n ν a t BState B0 := by
  let B : ℝ :=
    h3SelectedIntermediateSlabForcingBudget
      n BState B0

  have hB0' : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedIntermediateSlabForcingBudget_nonneg
        hBS hB0

  have hr0 : 0 ≤ r :=
    le_trans ha.le har

  have hLocalLag0 :
      0 ≤ r - r / 2 := by
    linarith

  have hGlobalLag0 :
      0 ≤ t - a / 2 := by
    linarith

  have hLag :
      r - r / 2 ≤ t - a / 2 := by
    linarith

  have hPow :
      (r - r / 2) ^ ((1 : ℝ) / 8)
        ≤
      (t - a / 2) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow
      hLocalLag0 hLag (by norm_num)

  have hScale0 :
      0 ≤
        8 *
          h3HeatSevenQuarterNormalizedCoefficient ν := by
    unfold h3HeatSevenQuarterNormalizedCoefficient
    positivity

  have hScaled :
      8 *
          h3HeatSevenQuarterNormalizedCoefficient ν *
          (r - r / 2) ^ ((1 : ℝ) / 8)
        ≤
      8 *
          h3HeatSevenQuarterNormalizedCoefficient ν *
          (t - a / 2) ^ ((1 : ℝ) / 8) :=
    mul_le_mul_of_nonneg_left hPow hScale0

  unfold
    h3SelectedIntermediateSlabTailBudget
    h3SelectedDuhamelSevenQuarterSourceBudget

  dsimp only [B] at hB0' hScaled ⊢

  exact
    mul_le_mul_of_nonneg_left
      hScaled hB0'

/-!
## First half-step: natural slab -> natural-plus-three-quarter slab
-/

/-- The first half of the generic moment bootstrap.

A natural `n`-moment slab on `[a/2,t]` with `1 ≤ n` produces an
`n+3/4`-moment slab on `[a,t]`.  The lower endpoint shrinks in the input
because every output terminal tail at time `r` samples source times down to
`r/2`. -/
theorem h3SelectedMomentSlab_nat_to_natAddThreeQuarter
    {ν A a t BState BDuhamel B0 : ℝ}
    (n : ℕ)
    (hn : 1 ≤ n)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hSlab :
      H3SelectedMomentSlab
        (n : ℝ) ν A (a / 2) t
        BState BDuhamel B0
        hν U₀ hA hU₀) :
    H3SelectedMomentSlab
      ((n : ℝ) + (3 : ℝ) / 4)
      ν A a t
      (h3SelectedIntermediateSlabStateBudget
        n ν A a t BState BDuhamel B0)
      (h3SelectedIntermediateSlabDuhamelBudget
        n ν a t BState BDuhamel B0)
      B0
      hν U₀ hA hU₀ := by
  have hSlabData := hSlab
  unfold H3SelectedMomentSlab at hSlabData
  rcases hSlabData with
    ⟨hBS0, hBD0, hB00, hData⟩

  have hnReal :
      (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hOut0 :
      0 ≤ (n : ℝ) + (3 : ℝ) / 4 := by
    positivity

  have hForce0 :
      0 ≤
        h3SelectedIntermediateSlabForcingBudget
          n BState B0 :=
    h3SelectedIntermediateSlabForcingBudget_nonneg
      hBS0 hB00

  have hDOut0 :
      0 ≤
        h3SelectedIntermediateSlabDuhamelBudget
          n ν a t BState BDuhamel B0 :=
    h3SelectedIntermediateSlabDuhamelBudget_nonneg
      hν ha hat hBS0 hBD0 hB00

  have hSOut0 :
      0 ≤
        h3SelectedIntermediateSlabStateBudget
          n ν A a t BState BDuhamel B0 :=
    h3SelectedIntermediateSlabStateBudget_nonneg
      hν hA ha hat hBS0 hBD0 hB00

  unfold H3SelectedMomentSlab
  refine ⟨hSOut0, hDOut0, hB00, ?_⟩

  intro r hr i
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := r) hν U₀ hA hU₀ i

  have hr0 : 0 < r :=
    lt_of_lt_of_le ha hr.1

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hr.2 htR

  have hhalf0 : 0 < r / 2 := by
    positivity

  have hhalfMem :
      r / 2 ∈ Set.Icc (a / 2) t := by
    constructor
    · linarith [hr.1]
    · have hrr : r / 2 ≤ r := by
        linarith
      exact le_trans hrr hr.2

  have hrInput :
      r ∈ Set.Icc (a / 2) t := by
    constructor
    · linarith [hr.1, ha]
    · exact hr.2

  have hHalfData :=
    hData (r / 2) hhalfMem i

  have hRData :=
    hData r hrInput i

  dsimp only [W] at hHalfData hRData

  have hDHalfInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (n : ℝ) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := r / 2) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHalfData.2.2.1

  have hDHalfLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := r / 2) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      BDuhamel :=
    hHalfData.2.2.2.1

  /- Midpoint head. -/

  let CHead : ℝ :=
    h3HeatThreeQuarterMomentCoefficient ν (a / 2)

  have ha2 : 0 < a / 2 := by
    positivity

  have hCHead0 : 0 ≤ CHead := by
    dsimp only [CHead]
    exact
      h3HeatThreeQuarterMomentCoefficient_nonneg
        hν.le ha2.le

  have hHeadBase :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight ((3 : ℝ) / 4) ξ *
            ‖h3HeatFourierSymbol ν (a / 2) ξ‖
          ≤
        CHead := by
    intro ξ
    dsimp only [CHead]
    simpa only [
      h3FourierMomentWeight,
      h3FourierThreeQuarterWeight
    ] using
      (norm_h3HeatFourierSymbol_threeQuarter_le
        hν ha2 ξ)

  have hHeadHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight ((3 : ℝ) / 4) ξ *
            ‖h3HeatFourierSymbol ν (r / 2) ξ‖
          ≤
        CHead := by
    intro ξ
    exact
      h3HeatFourierSymbol_momentBound_of_le_time
        hν ha2 (by linarith [hr.1]) hCHead0 hHeadBase ξ

  have hHeadInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ hr0 i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_moment_integrable_of_halfDuhamelMoment
        (q := (n : ℝ))
        (r := (3 : ℝ) / 4)
        (t := r)
        (C := CHead)
        (by positivity)
        (by norm_num)
        hν U₀ hA hU₀ hr0 i
        hCHead0 hHeadHeat hDHalfInt

  have hHeadLeBase :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ hr0 i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      CHead *
        (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := r / 2) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖) := by
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_moment_integral_le_of_halfDuhamelMoment
        (q := (n : ℝ))
        (r := (3 : ℝ) / 4)
        (t := r)
        (C := CHead)
        (by positivity)
        (by norm_num)
        hν U₀ hA hU₀ hr0 i
        hCHead0 hHeadHeat hDHalfInt

  have hHeadLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ hr0 i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedIntermediateSlabHeadBudget
        ν a BDuhamel := by
    unfold h3SelectedIntermediateSlabHeadBudget
    dsimp only [CHead] at hHeadLeBase ⊢
    exact
      le_trans hHeadLeBase
        (mul_le_mul_of_nonneg_left
          hDHalfLe
          (h3HeatThreeQuarterMomentCoefficient_nonneg
            hν.le ha2.le))

  /- Terminal tail. -/

  let BForce : ℝ :=
    h3SelectedIntermediateSlabForcingBudget
      n BState B0

  have hForcingInt :
      ∀ s ∈ Set.Ioo (r / 2) r,
        let W' : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight ((n : ℝ) - 1) ξ *
              ‖h3RawFinLerayOuterProductDivergence
                (W' s) (W' s) i ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro s hs

    have hsInput :
        s ∈ Set.Icc (a / 2) t := by
      constructor
      · linarith [hs.1, hr.1]
      · exact le_trans hs.2.le hr.2

    exact
      h3RawFinLerayOuterProductDivergence_selectedMomentSlab_subOneMoment_integrable
        (p := (n : ℝ))
        hnReal hν U₀ hA hU₀
        hSlab s hsInput i

  have hForcingMass :
      ∀ s ∈ Set.Ioo (r / 2) r,
        let W' : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceMomentMass
            ((n : ℝ) - 1) (W' s) (W' s) i
          ≤
        BForce := by
    intro s hs

    have hsInput :
        s ∈ Set.Icc (a / 2) t := by
      constructor
      · linarith [hs.1, hr.1]
      · exact le_trans hs.2.le hr.2

    dsimp only [BForce]

    exact
      h3RawFinLerayOuterProductDivergence_selectedMomentSlab_subOneMass_le
        (p := (n : ℝ))
        hnReal hν U₀ hA hU₀
        hSlab s hsInput i

  have hq0 :
      0 ≤ (n : ℝ) - 1 := by
    linarith

  have hTailProd0 :=
    h3SelectedDuhamel_addSevenQuarter_fubini_integrable_of_forcingMoment_le
      (q := (n : ℝ) - 1)
      (a := r / 2)
      (t := r)
      (B := BForce)
      hq0 hν U₀ hA hU₀
      (by linarith)
      (by
        dsimp only [BForce]
        exact hForce0)
      i hForcingInt hForcingMass

  have hOutEq :
      ((n : ℝ) - 1) + (7 : ℝ) / 4
        =
      (n : ℝ) + (3 : ℝ) / 4 := by
    ring

  have hTailProd :
      Integrable
        (h3SelectedDuhamelMomentComplexKernel
          ((n : ℝ) + (3 : ℝ) / 4)
          ν A r hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict
            (Set.Ioo (r / 2) r)).prod
          (volume : Measure H3FourierPoint3)) := by
    simpa only [hOutEq] using hTailProd0

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_moment_integrable_of_product
      (p := (n : ℝ) + (3 : ℝ) / 4)
      hν U₀ hA hU₀ hr0 i hTailProd

  have hTailIter0 :=
    h3SelectedDuhamel_addSevenQuarter_iteratedNormIntegral_le_of_forcingMoment_le
      (q := (n : ℝ) - 1)
      (a := r / 2)
      (t := r)
      (B := BForce)
      hq0 hν U₀ hA hU₀
      (by linarith)
      (by
        dsimp only [BForce]
        exact hForce0)
      i hForcingInt hForcingMass

  have hTailIter :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              ((n : ℝ) + (3 : ℝ) / 4)
              ν A r hν U₀ hA hU₀ i (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂((volume : Measure ℝ).restrict
          (Set.Ioo (r / 2) r)))
        ≤
      h3SelectedDuhamelSevenQuarterSourceBudget
        ν (r / 2) r BForce := by
    simpa only [hOutEq] using hTailIter0

  have hRawTailLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖h3SelectedDuhamelTailRawFourierAmplitude
              ν A r hν U₀ hA hU₀ i ξ‖)
        ≤
      h3SelectedDuhamelSevenQuarterSourceBudget
        ν (r / 2) r BForce :=
    integral_moment_h3SelectedDuhamelTailRawFourierAmplitude_le_of_budget
      (p := (n : ℝ) + (3 : ℝ) / 4)
      hν U₀ hA hU₀ i
      hTailProd hTailIter

  have hNamedTailLocal :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedDuhamelSevenQuarterSourceBudget
        ν (r / 2) r BForce :=
    integral_moment_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le_of_budget
      (p := (n : ℝ) + (3 : ℝ) / 4)
      hν U₀ hA hU₀ hr0 i hRawTailLe

  have hTailGlobal :
      h3SelectedDuhamelSevenQuarterSourceBudget
          ν (r / 2) r BForce
        ≤
      h3SelectedIntermediateSlabTailBudget
        n ν a t BState B0 := by
    dsimp only [BForce]
    exact
      h3SelectedDuhamelSevenQuarterSourceBudget_local_le_intermediateSlab
        hν ha hr.1 hr.2 hBS0 hB00

  have hTailLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedIntermediateSlabTailBudget
        n ν a t BState B0 :=
    le_trans hNamedTailLocal hTailGlobal

  /- Complete Duhamel. -/

  have hDuhamelInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_moment_integrable_of_head_tail
      hOut0 hν U₀ hA hU₀ hr0 i
      hHeadInt hTailInt

  have hDuhamelLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedIntermediateSlabDuhamelBudget
        n ν a t BState BDuhamel B0 := by
    unfold h3SelectedIntermediateSlabDuhamelBudget
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_moment_integral_le_of_head_tail
        hOut0 hν U₀ hA hU₀ hr0 i
        hHeadInt hTailInt hHeadLe hTailLe

  /- Free heat. -/

  let CHeat : ℝ :=
    h3HeatNatAddThreeQuarterMomentCoefficient
      n ν a

  have hCHeat0 : 0 ≤ CHeat := by
    dsimp only [CHeat]
    exact
      h3HeatNatAddThreeQuarterMomentCoefficient_nonneg
        n hν.le ha.le

  have hFreeBase :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight
            ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖h3HeatFourierSymbol ν a ξ‖
          ≤
        CHeat := by
    intro ξ
    dsimp only [CHeat]
    exact
      h3HeatFourierMomentMultiplier_le_nat_add_threeQuarter
        hν ha n ξ

  have hFreeHeatBound :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight
            ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖h3HeatFourierSymbol ν r ξ‖
          ≤
        CHeat := by
    intro ξ
    exact
      h3HeatFourierSymbol_momentBound_of_le_time
        hν ha hr.1 hCHeat0 hFreeBase ξ

  have hFreeInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ hr0 i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_moment_integrable_of_multiplier
      hOut0 hν U₀ hr0 i
      hCHeat0 hFreeHeatBound

  have hFreeLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ hr0 i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedIntermediateSlabHeatBudget
        n ν A a := by
    unfold h3SelectedIntermediateSlabHeatBudget
    have hFreeLeBase :=
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_moment_integral_le_of_multiplier
        hOut0 hν U₀ hA hU₀ hr0 i
        hCHeat0 hFreeHeatBound
    simpa only [CHeat] using hFreeLeBase

  /- Mild state and transfer to the canonical raw Fourier representative. -/

  have hNamedMildInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                hν U₀ hA hU₀ r i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_moment_integrable_of_heat_duhamel
      hOut0 hν U₀ hA hU₀ hr0 hrR i
      hFreeInt hDuhamelInt

  have hNamedMildLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + (3 : ℝ) / 4) ξ *
            ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                hν U₀ hA hU₀ r i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedIntermediateSlabStateBudget
        n ν A a t BState BDuhamel B0 := by
    unfold h3SelectedIntermediateSlabStateBudget
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_moment_integral_le_of_heat_duhamel
        hOut0 hν U₀ hA hU₀ hr0 hrR i
        hFreeInt hDuhamelInt
        hFreeLe hDuhamelLe

  have hRawMildInt :
      H3RawFourierMomentIntegrable
        ((n : ℝ) + (3 : ℝ) / 4)
        (W r i) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_moment_integrable_of_L2
        hν U₀ hA hU₀ i hNamedMildInt

  have hRawMildLe :
      h3SpectralScalarRawFourierMomentMass
          ((n : ℝ) + (3 : ℝ) / 4)
          (W r i)
        ≤
      h3SelectedIntermediateSlabStateBudget
        n ν A a t BState BDuhamel B0 := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_momentMass_le_of_L2
        hν U₀ hA hU₀ i hNamedMildLe

  have hL1 :
      h3SpectralScalarRawFourierL1Mass
          (W r i)
        ≤
      B0 := by
    dsimp only [W]
    exact hRData.2.2.2.2

  exact
    ⟨hRawMildInt,
      hRawMildLe,
      hDuhamelInt,
      hDuhamelLe,
      hL1⟩

end
end Euclidean
end Bridge
end PrimeTensor
