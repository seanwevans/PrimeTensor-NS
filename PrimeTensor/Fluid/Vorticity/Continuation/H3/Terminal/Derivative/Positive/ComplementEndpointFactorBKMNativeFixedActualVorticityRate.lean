import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeActualVorticityMaxRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeReindexCascade

/-!
# Fixed actual vorticity component on a native endpoint subsequence

The component attaining the actual-vorticity rate can change with the
native index. A finite-component extraction fixes one coordinate on a
cofinal subsequence. Reindexing preserves the full quantitative native
cascade and its near-terminal thresholds.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The actual logged vorticity component selected by one of three
fixed coordinate labels. -/
def h3NativeActualVorticityComponentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (i : Fin 3) (t : ℝ) (x : Point3) : ℝ :=
  if i = 0 then
    realVorticityX (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x
  else if i = 1 then
    realVorticityY (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x
  else
    realVorticityZ (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x

/-- An actual component above `n - 2` at every index yields one fixed
component above the reindexed threshold on a cofinal subsequence. -/
theorem native_actualVorticity_fixedComponent_extraction
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) (z : ℕ → Point3)
    (hComponent : ∀ n : ℕ,
      ((n : ℝ) - 2 <
        |realVorticityX (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ n) (z n)|) ∨
      ((n : ℝ) - 2 <
        |realVorticityY (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ n) (z n)|) ∨
      ((n : ℝ) - 2 <
        |realVorticityZ (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ n) (z n)|)) :
    ∃ i : Fin 3, ∃ k : ℕ → ℕ,
      (∀ n : ℕ, n ≤ k n) ∧
      (∀ n : ℕ,
        (n : ℝ) - 2 <
          |h3NativeActualVorticityComponentAt u i
            (τ (k n)) (z (k n))|) ∧
      Tendsto
        (fun n : ℕ =>
          |h3NativeActualVorticityComponentAt u i
            (τ (k n)) (z (k n))|)
        atTop atTop := by
  classical
  have hExists : ∀ n : ℕ,
      ∃ i : Fin 3,
        (n : ℝ) - 2 <
          |h3NativeActualVorticityComponentAt u i (τ n) (z n)| := by
    intro n
    rcases hComponent n with hx | hy | hz
    · refine ⟨0, ?_⟩
      simpa [h3NativeActualVorticityComponentAt] using hx
    · refine ⟨1, ?_⟩
      simpa [h3NativeActualVorticityComponentAt] using hy
    · refine ⟨2, ?_⟩
      simpa [h3NativeActualVorticityComponentAt] using hz
  choose i hi using hExists
  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop, ∃ q : Fin 3, i n = q :=
    Frequently.of_forall (fun n => ⟨i n, rfl⟩)
  obtain ⟨q, hFrequently⟩ :=
    (Filter.frequently_exists).1 hFrequentlySome
  obtain ⟨k, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop hFrequently
  have hk : ∀ n : ℕ, n ≤ k n := by
    intro n
    exact hMono.le_apply
  have hBound : ∀ n : ℕ,
      (n : ℝ) - 2 <
        |h3NativeActualVorticityComponentAt u q
          (τ (k n)) (z (k n))| := by
    intro n
    have hAt := hi (k n)
    rw [hFixed n] at hAt
    have hCast : (n : ℝ) ≤ (k n : ℝ) := by
      exact_mod_cast hk n
    linarith
  refine ⟨q, k, hk, hBound, ?_⟩
  refine tendsto_atTop.2 ?_
  intro C
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (C + 2)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith [hBound n]

/-- A single native witness carries either one fixed actual vorticity
component with a linear lower rate or exponential raw dissipation
growth. The actual-vorticity point may differ from the native point. -/
def H3TerminalPositiveGrowthFixedActualVorticityRateAlternative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) : Prop :=
  ∃ p : H3TerminalCurlGradientPair,
    ∃ sCurl sGradient : H3TerminalOrientation,
      ∃ τ : ℕ → ℝ,
        ∃ y : ℕ → Point3,
          H3TerminalPositiveGrowthQuantitativeNativeData
            u b T p sCurl sGradient τ y ∧
          ((∃ i : Fin 3, ∃ z : ℕ → Point3,
              (∀ n : ℕ,
                (n : ℝ) - 2 <
                  |h3NativeActualVorticityComponentAt u i (τ n) (z n)|) ∧
              Tendsto
                (fun n : ℕ =>
                  |h3NativeActualVorticityComponentAt u i (τ n) (z n)|)
                atTop atTop) ∨
            (∃ c : ℝ, 0 < c ∧
              ∀ᶠ n : ℕ in atTop,
                Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
                  velocityH3DissipationAt u (τ n)))

/-- Under nonextension, the fixed-coordinate rate alternative holds
on every strict terminal subtail. -/
theorem positiveGrowth_native_fixedActualVorticity_or_rawDissipation_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalPositiveGrowthFixedActualVorticityRateAlternative u b T := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hRate⟩ :=
    positiveGrowth_native_actualVorticity_or_rawDissipation_on_every_subtail
      hH3 hNoExtension hClass b hb
  rcases hRate with ⟨z, hComponent⟩ | hDissipation
  · obtain ⟨i, k, hk, hBound, hTop⟩ :=
      native_actualVorticity_fixedComponent_extraction
        u τ z hComponent
    exact ⟨p, sCurl, sGradient,
      (fun n => τ (k n)), (fun n => y (k n)),
      positiveGrowth_quantitativeNativeData_comp_cofinal hData hk,
      Or.inl ⟨i, (fun n => z (k n)), hBound, hTop⟩⟩
  · exact ⟨p, sCurl, sGradient, τ, y, hData,
      Or.inr hDissipation⟩

/-- Neutral continuation or a fixed actual vorticity component rate
or raw dissipation rate on each strict terminal subtail. -/
theorem smoothContinuationExtension_or_native_fixedActualVorticityRate_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalPositiveGrowthFixedActualVorticityRateAlternative u b T) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_native_fixedActualVorticity_or_rawDissipation_on_every_subtail
        hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
