import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Selected.Actual.Vorticity.Ratio
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Fixed.Actual.Vorticity.Rate

/-!
# Fixed actual component at the selected normalized rate

At every point the maximum of the three absolute vorticity components
is attained by one coordinate. Finite-component extraction fixes a
coordinate on a cofinal subsequence. The actual component then keeps
the divergent normalized rate, and its denominator retains the
original index of the supplied native witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- One of the three logged vorticity components attains their
pointwise maximum. -/
theorem exists_actualVorticityComponent_eq_maxAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (x : Point3) :
    ∃ i : Fin 3,
      h3NativeActualVorticityComponentMaxAt u t x =
        |h3NativeActualVorticityComponentAt u i t x| := by
  let X : ℝ :=
    |realVorticityX (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x|
  let Y : ℝ :=
    |realVorticityY (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x|
  let Z : ℝ :=
    |realVorticityZ (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x|
  by_cases hX : max Y Z ≤ X
  · refine ⟨0, ?_⟩
    change max X (max Y Z) = X
    exact max_eq_left hX
  · have hX' : X ≤ max Y Z := le_of_not_ge hX
    by_cases hY : Z ≤ Y
    · refine ⟨1, ?_⟩
      change max X (max Y Z) = Y
      rw [max_eq_right hX', max_eq_left hY]
    · have hY' : Y ≤ Z := le_of_not_ge hY
      refine ⟨2, ?_⟩
      change max X (max Y Z) = Z
      rw [max_eq_right hX', max_eq_right hY']

/-- Under a raw ceiling on one supplied native witness, a fixed
actual vorticity component has a divergent normalized square along
a cofinal native extraction. Its spatial points need not equal the
native curl-gradient points. -/
theorem positiveGrowth_native_fixedActualVorticityRatio_of_selectedRawCeiling
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
      (∀ n : ℕ,
        h3MinimalVorticityEnvelopeAt u (τ (m n)) - 1 <
          |h3NativeActualVorticityComponentAt u i (τ (m n)) (z n)|) ∧
      (∀ n : ℕ,
        (1 + |h3MinimalVorticityEnvelopeAt u (τ (m n))|) ^ 2 /
            ((m n : ℝ) + 1) ≤
          4 *
            ((1 + |h3NativeActualVorticityComponentAt u i
              (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1))) ∧
      (∀ n : ℕ,
        (n : ℝ) / 4 <
          (1 + |h3NativeActualVorticityComponentAt u i
            (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1)) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + |h3NativeActualVorticityComponentAt u i
            (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1))
        atTop atTop := by
  classical
  obtain ⟨k, z₀, hk, _hNative, hApprox, hCompare, hQuarter, hMaxTop⟩ :=
    positiveGrowth_native_actualVorticityRatio_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hData hRawCeiling
  have hExists : ∀ n : ℕ, ∃ i : Fin 3,
      h3NativeActualVorticityComponentMaxAt u (τ (k n)) (z₀ n) =
        |h3NativeActualVorticityComponentAt u i (τ (k n)) (z₀ n)| := by
    intro n
    exact exists_actualVorticityComponent_eq_maxAt u (τ (k n)) (z₀ n)
  choose i hi using hExists
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
  let m : ℕ → ℕ := fun n => k (l n)
  let z : ℕ → Point3 := fun n => z₀ (l n)
  have hm : ∀ n : ℕ, n ≤ m n := by
    intro n
    exact (hl n).trans (hk (l n))
  have hlTop : Tendsto l atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hl n)
  have hMaxEq : ∀ n : ℕ,
      h3NativeActualVorticityComponentMaxAt u (τ (m n)) (z n) =
        |h3NativeActualVorticityComponentAt u q (τ (m n)) (z n)| := by
    intro n
    have hAt := hi (l n)
    rw [hFixed n] at hAt
    exact hAt
  have hFixedApprox : ∀ n : ℕ,
      h3MinimalVorticityEnvelopeAt u (τ (m n)) - 1 <
        |h3NativeActualVorticityComponentAt u q (τ (m n)) (z n)| := by
    intro n
    have hAt := hApprox (l n)
    rw [hMaxEq n] at hAt
    exact hAt
  have hFixedCompare : ∀ n : ℕ,
      (1 + |h3MinimalVorticityEnvelopeAt u (τ (m n))|) ^ 2 /
          ((m n : ℝ) + 1) ≤
        4 *
          ((1 + |h3NativeActualVorticityComponentAt u q
            (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1)) := by
    intro n
    have hAt := hCompare (l n)
    rw [hMaxEq n] at hAt
    exact hAt
  have hFixedQuarter : ∀ n : ℕ,
      (n : ℝ) / 4 <
        (1 + |h3NativeActualVorticityComponentAt u q
          (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1) := by
    intro n
    have hAt := hQuarter (l n)
    rw [hMaxEq n] at hAt
    have hCast : (n : ℝ) ≤ (l n : ℝ) := by
      exact_mod_cast hl n
    linarith
  have hMaxSubTop :
      Tendsto
        (fun n : ℕ =>
          (1 + h3NativeActualVorticityComponentMaxAt u
            (τ (m n)) (z n)) ^ 2 / ((m n : ℝ) + 1))
        atTop atTop :=
    hMaxTop.comp hlTop
  have hFixedTop :
      Tendsto
        (fun n : ℕ =>
          (1 + |h3NativeActualVorticityComponentAt u q
            (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1))
        atTop atTop := by
    convert hMaxSubTop using 1
    funext n
    rw [hMaxEq n]
  exact ⟨q, m, z, hm,
    positiveGrowth_quantitativeNativeData_comp_cofinal hData hm,
    hFixedApprox, hFixedCompare, hFixedQuarter, hFixedTop⟩

end

end Euclidean
end Bridge
end PrimeTensor
