import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Selected.Enstrophy.Clock.Collapse

/-!
# Quantitative selected clock collapse under bounded physical enstrophy

The selected pointwise enstrophy theorem supplies the explicit lower
rate

`n / 8 - 1 < E n / (m n + 1)`.

If the corresponding physical-clock enstrophy product remains
eventually bounded, this forces more than qualitative clock collapse:
the dimensionless selected clock is `O(1 / n)`. Since the selected
native index satisfies `n ≤ m n`, the physical endpoint gap itself is
then `O(1 / n^2)`.

These are necessary consequences of the additional physical-enstrophy
ceiling; they do not supply that ceiling.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Under an eventual physical-clock pointwise enstrophy ceiling, the
selected native clock has an explicit inverse-extraction-index bound.
Consequently the selected physical endpoint gap has a quadratic
inverse-index bound. -/
theorem positiveGrowth_native_clockRate_of_boundedPhysicalEnstrophy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hRawCeiling : H3TerminalNativeRawSubexponentialCeilingOnWitness u τ)
    (hPhysicalCeiling : ∃ B : ℝ,
      ∀ᶠ j : ℕ in atTop, ∀ x : Point3,
        (T - τ j) *
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ j) x ≤ B) :
    ∃ i : Fin 3, ∃ m : ℕ → ℕ, ∃ z : ℕ → Point3, ∃ C : ℝ,
      0 ≤ C ∧
      (∀ n : ℕ, n ≤ m n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (m n)) (fun n => y (m n)) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + |h3NativeActualVorticityComponentAt u i
            (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ (m n)) (z n) / ((m n : ℝ) + 1))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          ((m n : ℝ) + 1) * (T - τ (m n)))
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ᶠ n : ℕ in atTop,
        (n : ℝ) *
            (((m n : ℝ) + 1) * (T - τ (m n))) ≤ C) ∧
      (∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ 2 * (T - τ (m n)) ≤ C) := by
  obtain ⟨i, m, z, hm, hNative, _hComponentRate,
    hComponentTop, hEnstrophyRate, hIndexed⟩ :=
    positiveGrowth_native_pointwiseEnstrophyRatio_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hData hRawCeiling
  obtain ⟨B, hBound⟩ := hPhysicalCeiling

  have hmTop : Tendsto m atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hm n)

  let F : ℕ → ℝ := fun n =>
    ((m n : ℝ) + 1) * (T - τ (m n))
  let R : ℕ → ℝ := fun n =>
    realEnstrophyDensity
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      (τ (m n)) (z n) / ((m n : ℝ) + 1)
  let P : ℕ → ℝ := fun n =>
    (T - τ (m n)) *
      realEnstrophyDensity
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        (τ (m n)) (z n)

  have hFNonneg : ∀ n : ℕ, 0 ≤ F n := by
    intro n
    have ht : τ (m n) < T := (hNative.1 n).1.2
    dsimp [F]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr ht.le)

  have hProduct : ∀ n : ℕ, F n * R n = P n := by
    intro n
    dsimp [F, R, P]
    have hDenNe : (m n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hDenNe] <;> ring

  have hPBound : ∀ᶠ n : ℕ in atTop, P n ≤ B := by
    filter_upwards [hmTop.eventually hBound] with n hn
    exact hn (z n)

  have hCollapse : Tendsto F atTop (𝓝 (0 : ℝ)) :=
    boundedProduct_forces_vanishing_clockFactor
      F R P B hFNonneg hIndexed hProduct hPBound

  let C : ℝ := 16 * max B 0

  have hCNonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (le_max_right B 0)

  have hClockRate :
      ∀ᶠ n : ℕ in atTop, (n : ℝ) * F n ≤ C := by
    filter_upwards [hPBound, eventually_ge_atTop 16] with n hnP hn16

    have hn16R : (16 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn16

    have hRate :
        (n : ℝ) / 8 - 1 < R n := by
      simpa [R] using hEnstrophyRate n

    have hLower :
        (n : ℝ) / 16 ≤ R n := by
      have hMid :
          (n : ℝ) / 16 ≤ (n : ℝ) / 8 - 1 := by
        linarith
      exact hMid.trans (le_of_lt hRate)

    have hScaled :
        F n * ((n : ℝ) / 16) ≤ max B 0 := by
      calc
        F n * ((n : ℝ) / 16) ≤ F n * R n :=
          mul_le_mul_of_nonneg_left hLower (hFNonneg n)
        _ = P n := hProduct n
        _ ≤ B := hnP
        _ ≤ max B 0 := le_max_left B 0

    calc
      (n : ℝ) * F n =
          16 * (F n * ((n : ℝ) / 16)) := by ring
      _ ≤ 16 * max B 0 :=
        mul_le_mul_of_nonneg_left hScaled (by norm_num)
      _ = C := by rfl

  have hGapRate :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ 2 * (T - τ (m n)) ≤ C := by
    filter_upwards [hClockRate] with n hn
    have hGapNonneg : 0 ≤ T - τ (m n) := by
      exact sub_nonneg.mpr (hNative.1 n).1.2.le
    have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmCast : (n : ℝ) ≤ (m n : ℝ) := by
      exact_mod_cast hm n
    have hIndex :
        (n : ℝ) ≤ (m n : ℝ) + 1 := by
      linarith
    have hCompare :
        (n : ℝ) * ((n : ℝ) * (T - τ (m n))) ≤
          ((m n : ℝ) + 1) *
            ((n : ℝ) * (T - τ (m n))) :=
      mul_le_mul_of_nonneg_right hIndex
        (mul_nonneg hnNonneg hGapNonneg)
    calc
      (n : ℝ) ^ 2 * (T - τ (m n)) =
          (n : ℝ) * ((n : ℝ) * (T - τ (m n))) := by ring
      _ ≤ ((m n : ℝ) + 1) *
          ((n : ℝ) * (T - τ (m n))) := hCompare
      _ = (n : ℝ) *
          (((m n : ℝ) + 1) * (T - τ (m n))) := by ring
      _ ≤ C := hn

  refine ⟨i, m, z, C, hCNonneg, hm, hNative,
    hComponentTop, hIndexed, ?_, ?_, hGapRate⟩
  · simpa [F] using hCollapse
  · simpa [F] using hClockRate

end

end Euclidean
end Bridge
end PrimeTensor
