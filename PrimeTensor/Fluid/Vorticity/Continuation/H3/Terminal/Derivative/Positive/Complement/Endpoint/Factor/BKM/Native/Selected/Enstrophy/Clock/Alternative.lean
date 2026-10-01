import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Selected.Enstrophy.Clock.Bridge

/-!
# Physical-clock alternative on a selected native witness

The indexed pointwise enstrophy rate admits an exact clock split.
Either the selected endpoint gaps are eventually bounded below by a
positive multiple of inverse original index, in which case the
physical-clock enstrophy product diverges, or a further cofinal
extraction makes that dimensionless clock factor tend to zero.
The second branch retains the native cascade and indexed enstrophy
rate. It does not assert a bound on the physical-clock product.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A nonnegative real sequence has either an eventual positive
lower bound or a cofinal extraction approaching zero. -/
theorem nonnegativeSequence_lowerBound_or_cofinal_zero
    (F : ℕ → ℝ) (hF : ∀ n : ℕ, 0 ≤ F n) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c ≤ F n) ∨
    (∃ l : ℕ → ℕ,
      (∀ n : ℕ, n ≤ l n) ∧
      (∀ n : ℕ, F (l n) < 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n : ℕ => F (l n)) atTop (𝓝 (0 : ℝ))) := by
  classical
  by_cases hLower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c ≤ F n
  · exact Or.inl hLower
  · have hPick : ∀ N : ℕ,
        ∃ j : ℕ, N ≤ j ∧ F j < 1 / ((N : ℝ) + 1) := by
      intro N
      by_contra hNone
      apply hLower
      refine ⟨1 / ((N : ℝ) + 1), by positivity, ?_⟩
      filter_upwards [eventually_ge_atTop N] with j hj
      have hNot : ¬ F j < 1 / ((N : ℝ) + 1) := by
        intro hSmall
        exact hNone ⟨j, hj, hSmall⟩
      exact le_of_not_gt hNot
    choose l hl using hPick
    have hInv :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hZero : Tendsto (fun n : ℕ => F (l n))
        atTop (𝓝 (0 : ℝ)) := by
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall (fun n => hF (l n))
      · exact Filter.Eventually.of_forall
          (fun n => le_of_lt (hl n).2)
      · exact hInv
    exact Or.inr ⟨l, (fun n => (hl n).1),
      (fun n => (hl n).2), hZero⟩

/-- Under a selected raw ceiling and hypothetical nonextension, the
indexed enstrophy rate yields either a divergent physical-clock
product or a cofinal native sequence whose dimensionless endpoint
clock collapses to zero. Both branches refer to the same selected
fixed actual-vorticity component and spatial points. -/
theorem positiveGrowth_native_enstrophy_physicalClockAlternative
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
    (hRawCeiling : H3TerminalNativeRawSubexponentialCeilingOnWitness u τ) :
    ∃ i : Fin 3, ∃ m : ℕ → ℕ, ∃ z : ℕ → Point3,
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
      (Tendsto
        (fun n : ℕ =>
          (T - τ (m n)) *
            realEnstrophyDensity
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ (m n)) (z n)) atTop atTop ∨
       ∃ l : ℕ → ℕ,
         (∀ n : ℕ, n ≤ l n) ∧
         H3TerminalPositiveGrowthQuantitativeNativeData
           u b T p sCurl sGradient
             (fun n => τ (m (l n))) (fun n => y (m (l n))) ∧
         Tendsto
           (fun n : ℕ =>
             realEnstrophyDensity
               (PrimeTensor.Bridge.logSpaceTimeVectorField u)
               (τ (m (l n))) (z (l n)) / ((m (l n) : ℝ) + 1))
           atTop atTop ∧
         (∀ n : ℕ,
           ((m (l n) : ℝ) + 1) * (T - τ (m (l n))) <
             1 / ((n : ℝ) + 1)) ∧
         Tendsto
           (fun n : ℕ =>
             ((m (l n) : ℝ) + 1) * (T - τ (m (l n))))
           atTop (𝓝 (0 : ℝ))) := by
  classical
  obtain ⟨i, m, z, hm, hNative, _hComponentRate,
    hComponentTop, _hEnstrophyRate, hIndexed⟩ :=
    positiveGrowth_native_pointwiseEnstrophyRatio_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hData hRawCeiling
  let F : ℕ → ℝ := fun n =>
    ((m n : ℝ) + 1) * (T - τ (m n))
  have hFNonneg : ∀ n : ℕ, 0 ≤ F n := by
    intro n
    have ht : τ (m n) < T := (hNative.1 n).1.2
    dsimp [F]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (le_of_lt ht))
  refine ⟨i, m, z, hm, hNative, hComponentTop, hIndexed, ?_⟩
  rcases nonnegativeSequence_lowerBound_or_cofinal_zero F hFNonneg with
      ⟨c, hc, hLower⟩ | ⟨l, hl, hSmall, hZero⟩
  · have hLowerClock : ∀ᶠ n : ℕ in atTop,
        c / ((m n : ℝ) + 1) ≤ T - τ (m n) := by
      filter_upwards [hLower] with n hn
      have hDenPos : 0 < (m n : ℝ) + 1 := by positivity
      exact (div_le_iff₀ hDenPos).2 (by simpa [F, mul_comm] using hn)
    have hENonneg : ∀ n : ℕ,
        0 ≤ realEnstrophyDensity
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ (m n)) (z n) := by
      intro n
      exact (sq_nonneg
        (h3NativeActualVorticityComponentAt u i (τ (m n)) (z n))).trans
          (native_actualVorticityComponent_sq_le_realEnstrophy
            u i (τ (m n)) (z n))
    exact Or.inl
      (indexedRate_to_physicalClockProduct_of_lowerClock
        (fun n : ℕ =>
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ (m n)) (z n))
        (fun n : ℕ => T - τ (m n)) m c hc hENonneg hIndexed
        hLowerClock)
  · have hNative' :=
      positiveGrowth_quantitativeNativeData_comp_cofinal hNative hl
    have hlTop : Tendsto l atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro N
      filter_upwards [eventually_ge_atTop N] with n hn
      exact le_trans hn (hl n)
    exact Or.inr ⟨l, hl, hNative', hIndexed.comp hlTop,
      hSmall, hZero⟩

end

end Euclidean
end Bridge
end PrimeTensor
