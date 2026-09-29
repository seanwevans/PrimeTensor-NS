import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSelectedEnstrophyClockAlternative

/-!
# Bounded physical enstrophy forces clock collapse

If a nonnegative clock factor times a divergent indexed rate stays
eventually bounded above, that clock factor tends to zero. Applied to
the selected native witness, an eventual physical-clock pointwise
enstrophy ceiling on its original times therefore forces the full
selected clock factor `(m n + 1) * (T - τ (m n))` to vanish. This is a
necessary condition under the additional ceiling, not an estimate
that supplies that ceiling or rules out clock collapse.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A bounded product with a factor tending to positive infinity
forces its nonnegative other factor to vanish. -/
theorem boundedProduct_forces_vanishing_clockFactor
    (F R P : ℕ → ℝ) (B : ℝ)
    (hFNonneg : ∀ n : ℕ, 0 ≤ F n)
    (hRTop : Tendsto R atTop atTop)
    (hProduct : ∀ n : ℕ, F n * R n = P n)
    (hPBound : ∀ᶠ n : ℕ in atTop, P n ≤ B) :
    Tendsto F atTop (𝓝 (0 : ℝ)) := by
  let C : ℝ := max B 0 + 1
  have hBLe : B ≤ C := by
    dsimp [C]
    linarith [le_max_left B (0 : ℝ)]
  have hInv : Tendsto (fun n : ℕ => (R n)⁻¹)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hRTop
  have hConst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) :=
    tendsto_const_nhds
  have hCInv : Tendsto (fun n : ℕ => C / R n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using hConst.mul hInv
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall hFNonneg
  · filter_upwards
      [hPBound, hRTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with n hn hRPos
    have hFR : F n * R n ≤ C :=
      (hProduct n).le.trans (hn.trans hBLe)
    exact (le_div_iff₀ hRPos).2 hFR
  · exact hCInv

/-- An eventual physical-clock pointwise enstrophy ceiling along the
supplied native witness forces clock collapse on its selected fixed-
component enstrophy sequence. The ceiling is uniform in the spatial
point, since that point is selected after the ceiling is assumed. -/
theorem positiveGrowth_native_clockCollapse_of_boundedPhysicalEnstrophy
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
      Tendsto
        (fun n : ℕ =>
          ((m n : ℝ) + 1) * (T - τ (m n)))
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨i, m, z, hm, hNative, _hComponentRate,
    hComponentTop, _hEnstrophyRate, hIndexed⟩ :=
    positiveGrowth_native_pointwiseEnstrophyRatio_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hData hRawCeiling
  obtain ⟨B, hBound⟩ := hPhysicalCeiling
  have hmTop : Tendsto m atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hm n)
  let F : ℕ → ℝ := fun n => ((m n : ℝ) + 1) * (T - τ (m n))
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
  exact ⟨i, m, z, hm, hNative, hComponentTop, hIndexed, hCollapse⟩

end

end Euclidean
end Bridge
end PrimeTensor
