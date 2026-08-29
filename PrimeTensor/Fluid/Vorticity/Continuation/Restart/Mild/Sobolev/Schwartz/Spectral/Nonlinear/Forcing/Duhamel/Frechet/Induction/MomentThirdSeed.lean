import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentNatIteration
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.UniformThirdMomentEnvelope

/-!
# Fréchet endpoint induction: cubic seed slab

The generic natural-moment recurrence is now closed.  What remains is to
connect it to the already-compiled named endpoint chain.

The fifth Fréchet layer proved one selected cubic state envelope valid
uniformly on every positive interval `[a,t]`.  The fourth layer already gives
pointwise cubic integrability and quantitative cubic Duhamel mass, while the
restart construction carries one time-independent raw Fourier `L¹` envelope.

This file packages those three facts into the generic slab invariant at
natural exponent `3`.

The bridge is intentionally thin:

* ordinary `‖ξ‖^3` is identified with the generic weight `w_3`;
* the named uniform state and Duhamel envelopes are enlarged by `max 0` so
  slab nonnegativity is automatic even for a degenerate closed interval;
* the existing restart `L¹` envelope is reused unchanged.

Combining this cubic seed with `MomentNatIteration` immediately yields every
natural Fourier moment `m ≥ 3` at every strictly positive lower time.

No new Fourier, heat, convolution, Fubini, or nonlinear estimate is proved
here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentThirdSeed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-!
## Cubic bridge into the generic moment language
-/

/-- The generic real-exponent weight at exponent three is the ordinary cubic
radial weight used by the named endpoint files. -/
theorem h3FourierMomentWeight_three
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight (3 : ℝ) ξ = ‖ξ‖ ^ 3 := by
  simpa using
    (h3FourierMomentWeight_natCast 3 ξ)

/-- The generic cubic state mass agrees exactly with the named cubic mass. -/
theorem h3SpectralScalarRawFourierMomentMass_three_eq
    (F : H3SpectralScalarState) :
    h3SpectralScalarRawFourierMomentMass (3 : ℝ) F
      =
    h3SpectralScalarRawFourierThirdMass F := by
  unfold
    h3SpectralScalarRawFourierMomentMass
    h3SpectralScalarRawFourierThirdMass
  simp only [h3FourierMomentWeight_three]

/-!
## Explicit cubic seed budgets
-/

/-- Slab-safe cubic state budget.  `max 0` avoids imposing a strict
nondegeneracy condition on the closed interval merely to prove that the
numerical budget is nonnegative. -/
noncomputable def h3SelectedThirdSeedStateBudget
    (ν A a t : ℝ) : ℝ :=
  max 0 (h3SelectedMildThirdMomentUniformEnvelope ν A a t)

/-- Slab-safe cubic Duhamel budget. -/
noncomputable def h3SelectedThirdSeedDuhamelBudget
    (ν A a t : ℝ) : ℝ :=
  max 0 (h3SelectedDuhamelThirdMomentUniformEnvelope ν A a t)

/-- The restart-wide raw Fourier `L¹` envelope used by the cubic seed. -/
noncomputable def h3SelectedThirdSeedL1Budget
    (A : ℝ) : ℝ :=
  h3SelectedRestartRawFourierL1Envelope A

theorem h3SelectedThirdSeedStateBudget_nonneg
    (ν A a t : ℝ) :
    0 ≤ h3SelectedThirdSeedStateBudget ν A a t := by
  unfold h3SelectedThirdSeedStateBudget
  exact le_max_left _ _

theorem h3SelectedThirdSeedDuhamelBudget_nonneg
    (ν A a t : ℝ) :
    0 ≤ h3SelectedThirdSeedDuhamelBudget ν A a t := by
  unfold h3SelectedThirdSeedDuhamelBudget
  exact le_max_left _ _

theorem h3SelectedThirdSeedL1Budget_nonneg
    {A : ℝ}
    (hA : 0 < A) :
    0 ≤ h3SelectedThirdSeedL1Budget A := by
  unfold h3SelectedThirdSeedL1Budget
  exact h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

/-!
## Cubic seed slab
-/

/-- The already-compiled endpoint hierarchy supplies the generic moment slab
at exponent three on every positive closed interval `[a,t]`. -/
theorem h3SelectedMomentSlab_three
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    H3SelectedMomentSlab
      (3 : ℝ) ν A a t
      (h3SelectedThirdSeedStateBudget ν A a t)
      (h3SelectedThirdSeedDuhamelBudget ν A a t)
      (h3SelectedThirdSeedL1Budget A)
      hν U₀ hA hU₀ := by
  unfold H3SelectedMomentSlab

  refine
    ⟨h3SelectedThirdSeedStateBudget_nonneg ν A a t,
      h3SelectedThirdSeedDuhamelBudget_nonneg ν A a t,
      h3SelectedThirdSeedL1Budget_nonneg hA,
      ?_⟩

  intro s hs i
  dsimp only

  have hs0 : 0 < s :=
    lt_of_lt_of_le ha hs.1

  have hsR :
      s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2 htR

  have hStateInt :
      H3RawFourierMomentIntegrable
        (3 : ℝ)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s i) := by
    unfold H3RawFourierMomentIntegrable
    simpa only [h3FourierMomentWeight_three] using
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMoment_integrable
        hν U₀ hA hU₀ hs0 hsR i)

  have hStateLegacy :
      h3SpectralScalarRawFourierThirdMass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s i)
        ≤
      h3SelectedMildThirdMomentUniformEnvelope ν A a t :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMass_le_uniform_on
      hν U₀ hA hU₀ ha hs.1 hs.2 htR i

  have hStateLe :
      h3SpectralScalarRawFourierMomentMass
          (3 : ℝ)
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s i)
        ≤
      h3SelectedThirdSeedStateBudget ν A a t := by
    rw [h3SpectralScalarRawFourierMomentMass_three_eq]
    unfold h3SelectedThirdSeedStateBudget
    exact
      le_trans hStateLegacy
        (le_max_right 0
          (h3SelectedMildThirdMomentUniformEnvelope ν A a t))

  have hDuhamelInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (3 : ℝ) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := s) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [h3FourierMomentWeight_three] using
      (h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ hs0 hsR i)

  have hDuhamelPoint :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := s) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedDuhamelThirdMomentEnvelope ν A s :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integral_le
      hν U₀ hA hU₀ hs0 hsR i

  have hDuhamelUniform :
      h3SelectedDuhamelThirdMomentEnvelope ν A s
        ≤
      h3SelectedDuhamelThirdMomentUniformEnvelope ν A a t :=
    h3SelectedDuhamelThirdMomentEnvelope_le_uniform_on
      hν U₀ hA hU₀ ha hs.1 hs.2 htR

  have hDuhamelLegacy :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := s) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedDuhamelThirdMomentUniformEnvelope ν A a t :=
    le_trans hDuhamelPoint hDuhamelUniform

  have hDuhamelGeneric :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (3 : ℝ) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := s) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedDuhamelThirdMomentUniformEnvelope ν A a t := by
    simpa only [h3FourierMomentWeight_three] using hDuhamelLegacy

  have hDuhamelLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (3 : ℝ) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := s) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤
      h3SelectedThirdSeedDuhamelBudget ν A a t := by
    unfold h3SelectedThirdSeedDuhamelBudget
    exact
      le_trans hDuhamelGeneric
        (le_max_right 0
          (h3SelectedDuhamelThirdMomentUniformEnvelope ν A a t))

  have hL1 :
      h3SpectralScalarRawFourierL1Mass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s i)
        ≤
      h3SelectedThirdSeedL1Budget A := by
    unfold h3SelectedThirdSeedL1Budget
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
        hν U₀ hA hU₀ s i

  exact
    ⟨hStateInt,
      hStateLe,
      hDuhamelInt,
      hDuhamelLe,
      hL1⟩

/-!
## Backstep geometry
-/

/-- Recursive induction backsteps never move a nonnegative target lower
endpoint to the right. -/
theorem h3SelectedMomentBackstep_le_self
    (k : ℕ)
    {a : ℝ}
    (ha : 0 ≤ a) :
    h3SelectedMomentBackstep k a ≤ a := by
  induction k generalizing a with
  | zero =>
      simp [h3SelectedMomentBackstep]
  | succ k ih =>
      rw [h3SelectedMomentBackstep]
      have ha4 : 0 ≤ a / 4 := by
        positivity
      have hk :
          h3SelectedMomentBackstep k (a / 4)
            ≤
          a / 4 :=
        ih ha4
      exact le_trans hk (by linarith)

/-!
## Every natural moment from the cubic seed
-/

/-- Every natural Fourier moment of order at least three is uniformly bounded
on every strictly positive closed time interval.

The named endpoint hierarchy supplies order three at the recursively earlier
positive lower endpoint; the generic natural iteration then transports that
seed to the requested order at lower endpoint `a`. -/
theorem h3SelectedMomentSlab_nat_ge_three
    {ν A a t : ℝ}
    (m : ℕ)
    (hm : 3 ≤ m)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    ∃ BState BDuhamel B0 : ℝ,
      H3SelectedMomentSlab
        (m : ℝ) ν A a t
        BState BDuhamel B0
        hν U₀ hA hU₀ := by
  let k : ℕ := m - 3
  let a₀ : ℝ := h3SelectedMomentBackstep k a

  have ha₀ : 0 < a₀ := by
    dsimp only [a₀]
    exact h3SelectedMomentBackstep_pos k ha

  have ha₀a : a₀ ≤ a := by
    dsimp only [a₀]
    exact h3SelectedMomentBackstep_le_self k ha.le

  have ha₀t : a₀ ≤ t :=
    le_trans ha₀a hat

  have hSeed :
      H3SelectedMomentSlab
        (3 : ℝ) ν A a₀ t
        (h3SelectedThirdSeedStateBudget ν A a₀ t)
        (h3SelectedThirdSeedDuhamelBudget ν A a₀ t)
        (h3SelectedThirdSeedL1Budget A)
        hν U₀ hA hU₀ :=
    h3SelectedMomentSlab_three
      hν U₀ hA hU₀ ha₀ ha₀t htR

  have hSeedNat :
      H3SelectedMomentSlab
        (((3 : ℕ) : ℝ)) ν A
        (h3SelectedMomentBackstep k a) t
        (h3SelectedThirdSeedStateBudget ν A a₀ t)
        (h3SelectedThirdSeedDuhamelBudget ν A a₀ t)
        (h3SelectedThirdSeedL1Budget A)
        hν U₀ hA hU₀ := by
    dsimp only [a₀] at hSeed ⊢
    simpa using hSeed

  have hIter :=
    h3SelectedMomentSlab_nat_iterate
      (BState :=
        h3SelectedThirdSeedStateBudget ν A a₀ t)
      (BDuhamel :=
        h3SelectedThirdSeedDuhamelBudget ν A a₀ t)
      (B0 :=
        h3SelectedThirdSeedL1Budget A)
      (3 : ℕ) k (by norm_num)
      hν U₀ hA hU₀
      ha hat htR hSeedNat

  obtain ⟨BState, BDuhamel, hOut⟩ := hIter

  refine
    ⟨BState, BDuhamel,
      h3SelectedThirdSeedL1Budget A,
      ?_⟩

  have hmk :
      3 + (m - 3) = m := by
    omega

  dsimp only [k] at hOut
  simpa only [hmk] using hOut

end
end Euclidean
end Bridge
end PrimeTensor
