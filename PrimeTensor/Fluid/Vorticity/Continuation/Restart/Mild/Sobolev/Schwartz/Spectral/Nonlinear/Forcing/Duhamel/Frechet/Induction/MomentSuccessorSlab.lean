import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentIntermediateSlab

/-!
# Fréchet endpoint induction: the uniform successor slab

The intermediate slab closes only the first half of the natural-moment
bootstrap.  The second half uses two already available slabs on the same
positive interval:

    M_n on [a,t]                    -- midpoint head input
    M_{n+3/4} on [a,t]              -- nonlinear tail input
      ->
    M_{n+1} on [2a,t].

The dependency is deliberately triangular.  The midpoint head at time `r`
uses the original natural `n` Duhamel moment at `r/2` and one full power of
positive-lag heat smoothing.  The terminal tail uses the intermediate
`n+3/4` state moment, hence forcing moment `n-1/4`; the generic residual
`5/4` source lift then lands exactly at `n+1`.

The lower endpoint doubles because every terminal half at output time `r`
must remain inside the common input slab: `r >= 2a` implies `r/2 >= a`.
The next file can compose this with the intermediate step at lower endpoint
`a/2`, yielding a complete natural successor from an input slab beginning at
`a/4`.

No named Fourier endpoint occurs in the theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentSuccessorSlab
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-!
## Uniform successor budgets
-/

/-- One slab-wide forcing constant generated from the incoming intermediate
`n+3/4` state moment and the common raw Fourier `L¹` bound. -/
noncomputable def h3SelectedSuccessorSlabForcingBudget
    (n : ℕ)
    (BIntermediateState B0 : ℝ) : ℝ :=
  h3SelectedMomentSlabForcingEnvelope
    ((n : ℝ) + (3 : ℝ) / 4)
    BIntermediateState B0

/-- The midpoint-head budget for the successor `n+1` Duhamel moment.  The
smallest available half-time heat lag is `a`. -/
noncomputable def h3SelectedSuccessorSlabHeadBudget
    (ν a BDuhamel : ℝ) : ℝ :=
  h3HeatOneMomentCoefficient ν a * BDuhamel

/-- One enlarged terminal-tail budget valid for every successor output time
`r ∈ [2a,t]`. -/
noncomputable def h3SelectedSuccessorSlabTailBudget
    (n : ℕ)
    (ν a t BIntermediateState B0 : ℝ) : ℝ :=
  h3SelectedDuhamelFiveQuarterSourceBudget
    ν a t
    (h3SelectedSuccessorSlabForcingBudget
      n BIntermediateState B0)

/-- Uniform complete-Duhamel budget at the successor exponent `n+1`. -/
noncomputable def h3SelectedSuccessorSlabDuhamelBudget
    (n : ℕ)
    (ν a t BIntermediateState BDuhamel B0 : ℝ) : ℝ :=
  h3SelectedSuccessorSlabHeadBudget ν a BDuhamel +
    h3SelectedSuccessorSlabTailBudget
      n ν a t BIntermediateState B0

/-- Uniform free-heat budget at natural exponent `n+1`, evaluated at the
smallest successor output heat time `2a`. -/
noncomputable def h3SelectedSuccessorSlabHeatBudget
    (n : ℕ)
    (ν A a : ℝ) : ℝ :=
  h3HeatNatMomentCoefficient (n + 1) ν (2 * a) *
    h3RawFourierL1DeweightingCoefficient *
    A

/-- Uniform mild-state budget at the successor exponent. -/
noncomputable def h3SelectedSuccessorSlabStateBudget
    (n : ℕ)
    (ν A a t BIntermediateState BDuhamel B0 : ℝ) : ℝ :=
  h3SelectedSuccessorSlabHeatBudget n ν A a +
    h3SelectedSuccessorSlabDuhamelBudget
      n ν a t BIntermediateState BDuhamel B0

theorem h3SelectedSuccessorSlabForcingBudget_nonneg
    {n : ℕ}
    {BIntermediateState B0 : ℝ}
    (hBS : 0 ≤ BIntermediateState)
    (hB0 : 0 ≤ B0) :
    0 ≤
      h3SelectedSuccessorSlabForcingBudget
        n BIntermediateState B0 := by
  unfold h3SelectedSuccessorSlabForcingBudget
  exact
    h3SelectedMomentSlabForcingEnvelope_nonneg
      hBS hB0

theorem h3SelectedSuccessorSlabHeadBudget_nonneg
    {ν a BDuhamel : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hBD : 0 ≤ BDuhamel) :
    0 ≤
      h3SelectedSuccessorSlabHeadBudget
        ν a BDuhamel := by
  unfold h3SelectedSuccessorSlabHeadBudget
  exact
    mul_nonneg
      (h3HeatOneMomentCoefficient_nonneg
        hν.le ha.le)
      hBD

theorem h3SelectedSuccessorSlabTailBudget_nonneg
    {n : ℕ}
    {ν a t BIntermediateState B0 : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hat : a ≤ t)
    (hBS : 0 ≤ BIntermediateState)
    (hB0 : 0 ≤ B0) :
    0 ≤
      h3SelectedSuccessorSlabTailBudget
        n ν a t BIntermediateState B0 := by
  have hForce0 :
      0 ≤
        h3SelectedSuccessorSlabForcingBudget
          n BIntermediateState B0 :=
    h3SelectedSuccessorSlabForcingBudget_nonneg
      hBS hB0

  have hLag0 :
      0 ≤ t - a := by
    linarith

  unfold
    h3SelectedSuccessorSlabTailBudget
    h3SelectedDuhamelFiveQuarterSourceBudget

  have hScale0 :
      0 ≤
        ((8 : ℝ) / 3) *
          h3HeatFiveQuarterNormalizedCoefficient ν *
          (t - a) ^ ((3 : ℝ) / 8) := by
    unfold h3HeatFiveQuarterNormalizedCoefficient
    positivity

  exact mul_nonneg hForce0 hScale0

theorem h3SelectedSuccessorSlabDuhamelBudget_nonneg
    {n : ℕ}
    {ν a t BIntermediateState BDuhamel B0 : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hat : a ≤ t)
    (hBS : 0 ≤ BIntermediateState)
    (hBD : 0 ≤ BDuhamel)
    (hB0 : 0 ≤ B0) :
    0 ≤
      h3SelectedSuccessorSlabDuhamelBudget
        n ν a t BIntermediateState BDuhamel B0 := by
  unfold h3SelectedSuccessorSlabDuhamelBudget
  exact
    add_nonneg
      (h3SelectedSuccessorSlabHeadBudget_nonneg
        hν ha hBD)
      (h3SelectedSuccessorSlabTailBudget_nonneg
        hν ha hat hBS hB0)

theorem h3SelectedSuccessorSlabHeatBudget_nonneg
    (n : ℕ)
    {ν A a : ℝ}
    (hA : 0 < A) :
    0 ≤
      h3SelectedSuccessorSlabHeatBudget
        n ν A a := by
  unfold h3SelectedSuccessorSlabHeatBudget
  exact
    mul_nonneg
      (mul_nonneg
        (h3HeatNatMomentCoefficient_nonneg
          (n + 1) ν (2 * a))
        h3RawFourierL1DeweightingCoefficient_nonneg)
      hA.le

theorem h3SelectedSuccessorSlabStateBudget_nonneg
    {n : ℕ}
    {ν A a t BIntermediateState BDuhamel B0 : ℝ}
    (hν : 0 < ν)
    (hA : 0 < A)
    (ha : 0 < a)
    (hat : a ≤ t)
    (hBS : 0 ≤ BIntermediateState)
    (hBD : 0 ≤ BDuhamel)
    (hB0 : 0 ≤ B0) :
    0 ≤
      h3SelectedSuccessorSlabStateBudget
        n ν A a t BIntermediateState BDuhamel B0 := by
  unfold h3SelectedSuccessorSlabStateBudget
  exact
    add_nonneg
      (h3SelectedSuccessorSlabHeatBudget_nonneg
        n hA)
      (h3SelectedSuccessorSlabDuhamelBudget_nonneg
        hν ha hat hBS hBD hB0)

/-!
## Local terminal-tail budget versus the one global successor budget
-/

/-- Every local `5/4` source budget occurring at `r ∈ [2a,t]` is bounded by
the one enlarged source budget on `(a,t)`. -/
theorem h3SelectedDuhamelFiveQuarterSourceBudget_local_le_successorSlab
    {n : ℕ}
    {ν a r t BIntermediateState B0 : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (h2ar : 2 * a ≤ r)
    (hrt : r ≤ t)
    (hBS : 0 ≤ BIntermediateState)
    (hB0 : 0 ≤ B0) :
    h3SelectedDuhamelFiveQuarterSourceBudget
        ν (r / 2) r
        (h3SelectedSuccessorSlabForcingBudget
          n BIntermediateState B0)
      ≤
    h3SelectedSuccessorSlabTailBudget
      n ν a t BIntermediateState B0 := by
  let B : ℝ :=
    h3SelectedSuccessorSlabForcingBudget
      n BIntermediateState B0

  have hB0' : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedSuccessorSlabForcingBudget_nonneg
        hBS hB0

  have hr0 : 0 ≤ r := by
    have h2a0 : 0 ≤ 2 * a := by
      positivity
    exact le_trans h2a0 h2ar

  have hLocalLag0 :
      0 ≤ r - r / 2 := by
    linarith

  have hGlobalLag0 :
      0 ≤ t - a := by
    linarith

  have hLag :
      r - r / 2 ≤ t - a := by
    linarith

  have hPow :
      (r - r / 2) ^ ((3 : ℝ) / 8)
        ≤
      (t - a) ^ ((3 : ℝ) / 8) :=
    Real.rpow_le_rpow
      hLocalLag0 hLag (by norm_num)

  have hScale0 :
      0 ≤
        ((8 : ℝ) / 3) *
          h3HeatFiveQuarterNormalizedCoefficient ν := by
    unfold h3HeatFiveQuarterNormalizedCoefficient
    positivity

  have hScaled :
      ((8 : ℝ) / 3) *
          h3HeatFiveQuarterNormalizedCoefficient ν *
          (r - r / 2) ^ ((3 : ℝ) / 8)
        ≤
      ((8 : ℝ) / 3) *
          h3HeatFiveQuarterNormalizedCoefficient ν *
          (t - a) ^ ((3 : ℝ) / 8) :=
    mul_le_mul_of_nonneg_left hPow hScale0

  unfold
    h3SelectedSuccessorSlabTailBudget
    h3SelectedDuhamelFiveQuarterSourceBudget

  dsimp only [B] at hB0' hScaled ⊢

  exact
    mul_le_mul_of_nonneg_left
      hScaled hB0'

/-!
## Second half-step: natural plus three-quarter slab -> natural successor slab
-/

/-- The second half of the generic natural-moment bootstrap.

A natural `n` slab and an intermediate `n+3/4` slab on the common interval
`[a,t]` produce an `n+1` slab on `[2a,t]`.  The natural slab supplies the
midpoint-head Duhamel moment at `r/2`; the intermediate slab supplies the
nonlinear forcing moment on the terminal source interval `(r/2,r)`. -/
theorem h3SelectedMomentSlab_natAddThreeQuarter_to_natSucc
    {ν A a t BState BDuhamel B0
      BIntermediateState BIntermediateDuhamel : ℝ}
    (n : ℕ)
    (hn : 1 ≤ n)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (h2at : 2 * a ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hNatSlab :
      H3SelectedMomentSlab
        (n : ℝ) ν A a t
        BState BDuhamel B0
        hν U₀ hA hU₀)
    (hIntermediateSlab :
      H3SelectedMomentSlab
        ((n : ℝ) + (3 : ℝ) / 4)
        ν A a t
        BIntermediateState BIntermediateDuhamel B0
        hν U₀ hA hU₀) :
    H3SelectedMomentSlab
      ((n : ℝ) + 1)
      ν A (2 * a) t
      (h3SelectedSuccessorSlabStateBudget
        n ν A a t BIntermediateState BDuhamel B0)
      (h3SelectedSuccessorSlabDuhamelBudget
        n ν a t BIntermediateState BDuhamel B0)
      B0
      hν U₀ hA hU₀ := by
  have hNatData := hNatSlab
  unfold H3SelectedMomentSlab at hNatData
  rcases hNatData with
    ⟨hNatBS0, hNatBD0, hB00, hNatSlices⟩

  have hIntermediateData := hIntermediateSlab
  unfold H3SelectedMomentSlab at hIntermediateData
  rcases hIntermediateData with
    ⟨hIntermediateBS0, _hIntermediateBD0, _hIntermediateB00,
      _hIntermediateSlices⟩

  have hnReal :
      (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hIntermediateOne :
      (1 : ℝ) ≤ (n : ℝ) + (3 : ℝ) / 4 := by
    linarith

  have hOut0 :
      0 ≤ (n : ℝ) + 1 := by
    positivity

  have hat : a ≤ t := by
    linarith

  have hForce0 :
      0 ≤
        h3SelectedSuccessorSlabForcingBudget
          n BIntermediateState B0 :=
    h3SelectedSuccessorSlabForcingBudget_nonneg
      hIntermediateBS0 hB00

  have hDOut0 :
      0 ≤
        h3SelectedSuccessorSlabDuhamelBudget
          n ν a t BIntermediateState BDuhamel B0 :=
    h3SelectedSuccessorSlabDuhamelBudget_nonneg
      hν ha hat hIntermediateBS0 hNatBD0 hB00

  have hSOut0 :
      0 ≤
        h3SelectedSuccessorSlabStateBudget
          n ν A a t BIntermediateState BDuhamel B0 :=
    h3SelectedSuccessorSlabStateBudget_nonneg
      hν hA ha hat hIntermediateBS0 hNatBD0 hB00

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

  have h2a0 : 0 < 2 * a := by
    positivity

  have hr0 : 0 < r :=
    lt_of_lt_of_le h2a0 hr.1

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hr.2 htR

  have hhalf0 : 0 < r / 2 := by
    positivity

  have hhalfMem :
      r / 2 ∈ Set.Icc a t := by
    constructor
    · linarith [hr.1]
    · have hrr : r / 2 ≤ r := by
        linarith
      exact le_trans hrr hr.2

  have hrInput :
      r ∈ Set.Icc a t := by
    constructor
    · linarith [hr.1, ha]
    · exact hr.2

  have hNatHalfData :=
    hNatSlices (r / 2) hhalfMem i

  have hNatRData :=
    hNatSlices r hrInput i

  dsimp only [W] at hNatHalfData hNatRData

  have hDHalfInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (n : ℝ) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := r / 2) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hNatHalfData.2.2.1

  have hDHalfLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := r / 2) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      BDuhamel :=
    hNatHalfData.2.2.2.1

  /- Midpoint head: reuse the original natural moment and add one heat power. -/

  let CHead : ℝ :=
    h3HeatOneMomentCoefficient ν a

  have hCHead0 : 0 ≤ CHead := by
    dsimp only [CHead]
    exact
      h3HeatOneMomentCoefficient_nonneg
        hν.le ha.le

  have hHeadBase :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (1 : ℝ) ξ *
            ‖h3HeatFourierSymbol ν a ξ‖
          ≤
        CHead := by
    intro ξ
    dsimp only [CHead]
    simpa only [
      h3FourierMomentWeight,
      Real.rpow_one
    ] using
      (norm_h3HeatFourierSymbol_oneMoment_le
        hν ha ξ)

  have hHeadHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (1 : ℝ) ξ *
            ‖h3HeatFourierSymbol ν (r / 2) ξ‖
          ≤
        CHead := by
    intro ξ
    exact
      h3HeatFourierSymbol_momentBound_of_le_time
        hν ha (by linarith [hr.1]) hCHead0 hHeadBase ξ

  have hHeadInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight
              ((n : ℝ) + 1) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ hr0 i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_moment_integrable_of_halfDuhamelMoment
        (q := (n : ℝ))
        (r := (1 : ℝ))
        (t := r)
        (C := CHead)
        (by positivity)
        (by norm_num)
        hν U₀ hA hU₀ hr0 i
        hCHead0 hHeadHeat hDHalfInt

  have hHeadLeBase :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + 1) ξ *
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
        (r := (1 : ℝ))
        (t := r)
        (C := CHead)
        (by positivity)
        (by norm_num)
        hν U₀ hA hU₀ hr0 i
        hCHead0 hHeadHeat hDHalfInt

  have hHeadLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + 1) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ hr0 i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedSuccessorSlabHeadBudget
        ν a BDuhamel := by
    unfold h3SelectedSuccessorSlabHeadBudget
    dsimp only [CHead] at hHeadLeBase ⊢
    exact
      le_trans hHeadLeBase
        (mul_le_mul_of_nonneg_left
          hDHalfLe
          (h3HeatOneMomentCoefficient_nonneg
            hν.le ha.le))

  /- Terminal tail: intermediate state moment -> forcing n-1/4 -> add 5/4. -/

  let BForce : ℝ :=
    h3SelectedSuccessorSlabForcingBudget
      n BIntermediateState B0

  have hForcingInt :
      ∀ s ∈ Set.Ioo (r / 2) r,
        let W' : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight
                (((n : ℝ) + (3 : ℝ) / 4) - 1) ξ *
              ‖h3RawFinLerayOuterProductDivergence
                (W' s) (W' s) i ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro s hs

    have hsInput :
        s ∈ Set.Icc a t := by
      constructor
      · linarith [hs.1, hr.1]
      · exact le_trans hs.2.le hr.2

    exact
      h3RawFinLerayOuterProductDivergence_selectedMomentSlab_subOneMoment_integrable
        (p := (n : ℝ) + (3 : ℝ) / 4)
        hIntermediateOne hν U₀ hA hU₀
        hIntermediateSlab s hsInput i

  have hForcingMass :
      ∀ s ∈ Set.Ioo (r / 2) r,
        let W' : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceMomentMass
            (((n : ℝ) + (3 : ℝ) / 4) - 1)
            (W' s) (W' s) i
          ≤
        BForce := by
    intro s hs

    have hsInput :
        s ∈ Set.Icc a t := by
      constructor
      · linarith [hs.1, hr.1]
      · exact le_trans hs.2.le hr.2

    dsimp only [BForce]

    exact
      h3RawFinLerayOuterProductDivergence_selectedMomentSlab_subOneMass_le
        (p := (n : ℝ) + (3 : ℝ) / 4)
        hIntermediateOne hν U₀ hA hU₀
        hIntermediateSlab s hsInput i

  have hq0 :
      0 ≤ ((n : ℝ) + (3 : ℝ) / 4) - 1 := by
    linarith

  have hTailProd0 :=
    h3SelectedDuhamel_addFiveQuarter_fubini_integrable_of_forcingMoment_le
      (q := ((n : ℝ) + (3 : ℝ) / 4) - 1)
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
      (((n : ℝ) + (3 : ℝ) / 4) - 1) + (5 : ℝ) / 4
        =
      (n : ℝ) + 1 := by
    ring

  have hTailProd :
      Integrable
        (h3SelectedDuhamelMomentComplexKernel
          ((n : ℝ) + 1)
          ν A r hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict
            (Set.Ioo (r / 2) r)).prod
          (volume : Measure H3FourierPoint3)) := by
    simpa only [hOutEq] using hTailProd0

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight
              ((n : ℝ) + 1) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_moment_integrable_of_product
      (p := (n : ℝ) + 1)
      hν U₀ hA hU₀ hr0 i hTailProd

  have hTailIter0 :=
    h3SelectedDuhamel_addFiveQuarter_iteratedNormIntegral_le_of_forcingMoment_le
      (q := ((n : ℝ) + (3 : ℝ) / 4) - 1)
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
              ((n : ℝ) + 1)
              ν A r hν U₀ hA hU₀ i (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂((volume : Measure ℝ).restrict
          (Set.Ioo (r / 2) r)))
        ≤
      h3SelectedDuhamelFiveQuarterSourceBudget
        ν (r / 2) r BForce := by
    simpa only [hOutEq] using hTailIter0

  have hRawTailLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + 1) ξ *
            ‖h3SelectedDuhamelTailRawFourierAmplitude
              ν A r hν U₀ hA hU₀ i ξ‖)
        ≤
      h3SelectedDuhamelFiveQuarterSourceBudget
        ν (r / 2) r BForce :=
    integral_moment_h3SelectedDuhamelTailRawFourierAmplitude_le_of_budget
      (p := (n : ℝ) + 1)
      hν U₀ hA hU₀ i
      hTailProd hTailIter

  have hNamedTailLocal :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + 1) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedDuhamelFiveQuarterSourceBudget
        ν (r / 2) r BForce :=
    integral_moment_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le_of_budget
      (p := (n : ℝ) + 1)
      hν U₀ hA hU₀ hr0 i hRawTailLe

  have hTailGlobal :
      h3SelectedDuhamelFiveQuarterSourceBudget
          ν (r / 2) r BForce
        ≤
      h3SelectedSuccessorSlabTailBudget
        n ν a t BIntermediateState B0 := by
    dsimp only [BForce]
    exact
      h3SelectedDuhamelFiveQuarterSourceBudget_local_le_successorSlab
        hν ha hr.1 hr.2 hIntermediateBS0 hB00

  have hTailLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight
              ((n : ℝ) + 1) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedSuccessorSlabTailBudget
        n ν a t BIntermediateState B0 :=
    le_trans hNamedTailLocal hTailGlobal

  /- Complete Duhamel. -/

  have hDuhamelInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight
              ((n : ℝ) + 1) ξ *
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
              ((n : ℝ) + 1) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedSuccessorSlabDuhamelBudget
        n ν a t BIntermediateState BDuhamel B0 := by
    unfold h3SelectedSuccessorSlabDuhamelBudget
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_moment_integral_le_of_head_tail
        hOut0 hν U₀ hA hU₀ hr0 i
        hHeadInt hTailInt hHeadLe hTailLe

  /- Free heat at the next natural moment. -/

  let CHeat : ℝ :=
    h3HeatNatMomentCoefficient (n + 1) ν (2 * a)

  have hCHeat0 : 0 ≤ CHeat := by
    dsimp only [CHeat]
    exact
      h3HeatNatMomentCoefficient_nonneg
        (n + 1) ν (2 * a)

  have hFreeBase :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight
            ((n : ℝ) + 1) ξ *
            ‖h3HeatFourierSymbol ν (2 * a) ξ‖
          ≤
        CHeat := by
    intro ξ
    dsimp only [CHeat]
    have hBase :=
      h3HeatFourierMomentMultiplier_le_nat
        hν h2a0 (n + 1) ξ
    simpa only [Nat.cast_add, Nat.cast_one] using hBase

  have hFreeHeatBound :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight
            ((n : ℝ) + 1) ξ *
            ‖h3HeatFourierSymbol ν r ξ‖
          ≤
        CHeat := by
    intro ξ
    exact
      h3HeatFourierSymbol_momentBound_of_le_time
        hν h2a0 hr.1 hCHeat0 hFreeBase ξ

  have hFreeInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight
              ((n : ℝ) + 1) ξ *
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
              ((n : ℝ) + 1) ξ *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ hr0 i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedSuccessorSlabHeatBudget
        n ν A a := by
    unfold h3SelectedSuccessorSlabHeatBudget
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
              ((n : ℝ) + 1) ξ *
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
              ((n : ℝ) + 1) ξ *
            ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                hν U₀ hA hU₀ r i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedSuccessorSlabStateBudget
        n ν A a t BIntermediateState BDuhamel B0 := by
    unfold h3SelectedSuccessorSlabStateBudget
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_moment_integral_le_of_heat_duhamel
        hOut0 hν U₀ hA hU₀ hr0 hrR i
        hFreeInt hDuhamelInt
        hFreeLe hDuhamelLe

  have hRawMildInt :
      H3RawFourierMomentIntegrable
        ((n : ℝ) + 1)
        (W r i) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_moment_integrable_of_L2
        hν U₀ hA hU₀ i hNamedMildInt

  have hRawMildLe :
      h3SpectralScalarRawFourierMomentMass
          ((n : ℝ) + 1)
          (W r i)
        ≤
      h3SelectedSuccessorSlabStateBudget
        n ν A a t BIntermediateState BDuhamel B0 := by
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
    exact hNatRData.2.2.2.2

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
