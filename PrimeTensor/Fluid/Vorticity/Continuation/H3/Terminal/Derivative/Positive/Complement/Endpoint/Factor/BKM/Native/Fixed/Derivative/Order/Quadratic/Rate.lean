import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Positive.Derivative.Quadratic.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Selected.Fixed.Actual.Vorticity.Ratio

/-!
# Fixed derivative order on the quadratic H³ physical-clock sequence

The positive-derivative quadratic sequence carries

`n (n + 1) - C < E₁ + E₂ + E₃`

eventually.  At each time one of the three derivative orders therefore carries
at least one third of the aggregate positive-derivative energy.  Finite-order
extraction fixes one order on a cofinal subsequence.

Because the extraction index is cofinal and dominates the new index, the
terminal localization, physical-clock lower bound, and quadratic full-energy
rate all survive.  The fixed derivative order then has an eventual one-third
quadratic lower rate and tends to `+∞`.

These remain necessary consequences conditional on hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The positive derivative energy block selected by a finite order index:
`0 ↦ E₁`, `1 ↦ E₂`, `2 ↦ E₃`. -/
def h3PositiveDerivativeEnergyOrderAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (q : Fin 3)
    (t : ℝ) : ℝ :=
  if q = 0 then
    velocityH3Energy1At u t
  else if q = 1 then
    velocityH3Energy2At u t
  else
    velocityH3Energy3At u t

/-- One of the three positive derivative-energy orders carries at least one
third of their sum. -/
theorem exists_h3PositiveDerivativeEnergyOrder_ge_third
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    ∃ q : Fin 3,
      (velocityH3Energy1At u t +
          velocityH3Energy2At u t +
          velocityH3Energy3At u t) / 3 ≤
        h3PositiveDerivativeEnergyOrderAt u q t := by
  by_cases h1 :
      (velocityH3Energy1At u t +
          velocityH3Energy2At u t +
          velocityH3Energy3At u t) / 3 ≤
        velocityH3Energy1At u t
  · refine ⟨0, ?_⟩
    simpa [h3PositiveDerivativeEnergyOrderAt] using h1
  · have h1' :
        velocityH3Energy1At u t <
          (velocityH3Energy1At u t +
              velocityH3Energy2At u t +
              velocityH3Energy3At u t) / 3 :=
      lt_of_not_ge h1
    by_cases h2 :
        (velocityH3Energy1At u t +
            velocityH3Energy2At u t +
            velocityH3Energy3At u t) / 3 ≤
          velocityH3Energy2At u t
    · refine ⟨1, ?_⟩
      simpa [h3PositiveDerivativeEnergyOrderAt] using h2
    · have h2' :
          velocityH3Energy2At u t <
            (velocityH3Energy1At u t +
                velocityH3Energy2At u t +
                velocityH3Energy3At u t) / 3 :=
        lt_of_not_ge h2
      refine ⟨2, ?_⟩
      have h3 :
          (velocityH3Energy1At u t +
              velocityH3Energy2At u t +
              velocityH3Energy3At u t) / 3 ≤
            velocityH3Energy3At u t := by
        linarith
      simpa [h3PositiveDerivativeEnergyOrderAt] using h3

/-- Under hypothetical nonextension, one fixed positive derivative order
carries a quadratic lower rate on a cofinal refinement of the physical-clock
sequence. -/
theorem exists_h3PositiveDerivativeEnergy_fixedOrderQuadraticRateSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ q : Fin 3, ∃ τ : ℕ → ℝ, ∃ C : ℝ,
      0 ≤ C ∧
      (∀ n : ℕ,
        τ n ∈ Set.Ioo a T ∧
        τ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          (T - τ n) * velocityH3EnergyAt u (τ n) ∧
        (n : ℝ) * ((n : ℝ) + 1) <
          velocityH3EnergyAt u (τ n)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ᶠ n : ℕ in atTop,
        ((n : ℝ) * ((n : ℝ) + 1) - C) / 3 <
          h3PositiveDerivativeEnergyOrderAt u q (τ n)) ∧
      Tendsto
        (fun n : ℕ =>
          h3PositiveDerivativeEnergyOrderAt u q (τ n))
        atTop atTop := by
  classical

  obtain ⟨σ, C, hCNonneg, hσ, hSigmaTendsto, hPositiveRate, _hPositiveTop⟩ :=
    exists_h3PositiveDerivativeEnergy_quadraticRateSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  have hOrderExists :
      ∀ n : ℕ, ∃ q : Fin 3,
        (velocityH3Energy1At u (σ n) +
            velocityH3Energy2At u (σ n) +
            velocityH3Energy3At u (σ n)) / 3 ≤
          h3PositiveDerivativeEnergyOrderAt u q (σ n) := by
    intro n
    exact exists_h3PositiveDerivativeEnergyOrder_ge_third u (σ n)

  choose i hi using hOrderExists

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop, ∃ q : Fin 3, i n = q :=
    Frequently.of_forall (fun n => ⟨i n, rfl⟩)

  obtain ⟨q, hFrequently⟩ :=
    (Filter.frequently_exists).1 hFrequentlySome

  obtain ⟨l, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop hFrequently

  have hl : ∀ n : ℕ, n ≤ l n := by
    intro n
    exact hMono.le_apply

  have hlTop : Tendsto l atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hl n)

  let τ : ℕ → ℝ := fun n => σ (l n)

  have hTauData :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T ∧
        τ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          (T - τ n) * velocityH3EnergyAt u (τ n) ∧
        (n : ℝ) * ((n : ℝ) + 1) <
          velocityH3EnergyAt u (τ n) := by
    intro n

    have hOld := hσ (l n)
    have hCast : (n : ℝ) ≤ (l n : ℝ) := by
      exact_mod_cast hl n

    have hDenN : 0 < (n : ℝ) + 1 := by
      positivity

    have hInv :
        (1 : ℝ) / ((l n : ℝ) + 1) ≤
          1 / ((n : ℝ) + 1) := by
      exact
        one_div_le_one_div_of_le
          hDenN
          (by linarith)

    have hNear :
        τ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T := by
      dsimp only [τ]
      constructor
      · linarith [hOld.2.1.1]
      · exact hOld.2.1.2

    have hClock :
        (n : ℝ) <
          (T - τ n) * velocityH3EnergyAt u (τ n) := by
      dsimp only [τ]
      exact lt_of_le_of_lt hCast hOld.2.2.1

    have hQuadIndex :
        (n : ℝ) * ((n : ℝ) + 1) ≤
          (l n : ℝ) * ((l n : ℝ) + 1) := by
      have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hlNonneg : 0 ≤ (l n : ℝ) := Nat.cast_nonneg (l n)
      nlinarith

    have hEnergy :
        (n : ℝ) * ((n : ℝ) + 1) <
          velocityH3EnergyAt u (τ n) := by
      dsimp only [τ]
      exact lt_of_le_of_lt hQuadIndex hOld.2.2.2

    exact ⟨hOld.1, hNear, hClock, hEnergy⟩

  have hTauTendsto : Tendsto τ atTop (𝓝 T) := by
    dsimp only [τ]
    exact hSigmaTendsto.comp hlTop

  have hPositiveRateComp :
      ∀ᶠ n : ℕ in atTop,
        (l n : ℝ) * ((l n : ℝ) + 1) - C <
          velocityH3Energy1At u (σ (l n)) +
          velocityH3Energy2At u (σ (l n)) +
          velocityH3Energy3At u (σ (l n)) :=
    hlTop.eventually hPositiveRate

  have hFixedRate :
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) * ((n : ℝ) + 1) - C) / 3 <
          h3PositiveDerivativeEnergyOrderAt u q (τ n) := by
    filter_upwards [hPositiveRateComp] with n hRateN

    have hOrder := hi (l n)
    rw [hFixed n] at hOrder

    have hCast : (n : ℝ) ≤ (l n : ℝ) := by
      exact_mod_cast hl n

    have hQuadIndex :
        (n : ℝ) * ((n : ℝ) + 1) ≤
          (l n : ℝ) * ((l n : ℝ) + 1) := by
      have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hlNonneg : 0 ≤ (l n : ℝ) := Nat.cast_nonneg (l n)
      nlinarith

    dsimp only [τ]
    nlinarith

  have hFixedTop :
      Tendsto
        (fun n : ℕ =>
          h3PositiveDerivativeEnergyOrderAt u q (τ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    obtain ⟨N : ℕ, hN⟩ :=
      exists_nat_gt (max (3 * M + C) 0 + 1)

    filter_upwards [hFixedRate, eventually_ge_atTop N] with n hRateN hn

    have hCast : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn

    have hNPos : 0 < (N : ℝ) := by
      have hMaxNonneg : 0 ≤ max (3 * M + C) 0 :=
        le_max_right _ _
      linarith

    have hnPos : 0 < (n : ℝ) :=
      lt_of_lt_of_le hNPos hCast

    have hMRaw : 3 * M + C < (n : ℝ) := by
      have hLeMax : 3 * M + C ≤ max (3 * M + C) 0 :=
        le_max_left _ _
      linarith

    have hQuadAbove :
        (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
      nlinarith

    have hThreshold :
        M < ((n : ℝ) * ((n : ℝ) + 1) - C) / 3 := by
      nlinarith

    exact le_of_lt (lt_trans hThreshold hRateN)

  exact
    ⟨
      q,
      τ,
      C,
      hCNonneg,
      hTauData,
      hTauTendsto,
      hFixedRate,
      hFixedTop
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
