import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Selected.Enstrophy.Clock.Gap

/-!
# Conditional physical-clock transfer for selected enstrophy

The native near-terminal window provides an upper bound on the time
remaining to the endpoint. To turn a divergent indexed pointwise
enstrophy ratio into a divergent physical-clock product, one needs a
lower bound on that time relative to the original witness index.
This module states the scalar transfer and applies it to a selected
native witness under an explicit eventual lower-clock assumption.
It does not derive that assumption from the H³ path data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A positive lower comparison between endpoint time and inverse
native index transfers divergent indexed nonnegative data to the
physical-clock product. -/
theorem indexedRate_to_physicalClockProduct_of_lowerClock
    (E δ : ℕ → ℝ) (m : ℕ → ℕ) (c : ℝ)
    (hc : 0 < c)
    (hENonneg : ∀ n : ℕ, 0 ≤ E n)
    (hIndexed : Tendsto
      (fun n : ℕ => E n / ((m n : ℝ) + 1)) atTop atTop)
    (hLower : ∀ᶠ n : ℕ in atTop,
      c / ((m n : ℝ) + 1) ≤ δ n) :
    Tendsto (fun n : ℕ => δ n * E n) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards
    [hIndexed.eventually (eventually_ge_atTop (M / c)), hLower]
    with n hn hδ
  have hScaled : M ≤ c * (E n / ((m n : ℝ) + 1)) := by
    calc
      M = c * (M / c) := by
        field_simp [ne_of_gt hc] <;> ring
      _ ≤ c * (E n / ((m n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hn (le_of_lt hc)
  have hProduct :
      c * (E n / ((m n : ℝ) + 1)) ≤ δ n * E n := by
    calc
      c * (E n / ((m n : ℝ) + 1)) =
          (c / ((m n : ℝ) + 1)) * E n := by ring
      _ ≤ δ n * E n :=
        mul_le_mul_of_nonneg_right hδ (hENonneg n)
  exact hScaled.trans hProduct

/-- If the original native witness has an eventual lower physical
clock comparable to inverse index, its selected pointwise enstrophy
has a divergent physical-clock product at the same selected points.
The clock assumption is on the supplied original witness, before
the cofinal extraction is chosen. -/
theorem positiveGrowth_native_physicalEnstrophy_of_selectedRawCeiling_lowerClock
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
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ᶠ j : ℕ in atTop,
      c / ((j : ℝ) + 1) ≤ T - τ j) :
    ∃ i : Fin 3, ∃ m : ℕ → ℕ, ∃ z : ℕ → Point3,
      (∀ n : ℕ, n ≤ m n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (m n)) (fun n => y (m n)) ∧
      Tendsto
        (fun n : ℕ =>
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ (m n)) (z n) / ((m n : ℝ) + 1))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (T - τ (m n)) *
            realEnstrophyDensity
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ (m n)) (z n))
        atTop atTop := by
  obtain ⟨i, m, z, hm, hNative, _hComponentRate,
    _hComponentTop, _hEnstrophyRate, hIndexed⟩ :=
    positiveGrowth_native_pointwiseEnstrophyRatio_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hData hRawCeiling
  have hmTop : Tendsto m atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hm n)
  have hLowerSelected : ∀ᶠ n : ℕ in atTop,
      c / ((m n : ℝ) + 1) ≤ T - τ (m n) :=
    hmTop.eventually hLower
  have hENonneg : ∀ n : ℕ,
      0 ≤ realEnstrophyDensity
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        (τ (m n)) (z n) := by
    intro n
    exact (sq_nonneg
      (h3NativeActualVorticityComponentAt u i (τ (m n)) (z n))).trans
        (native_actualVorticityComponent_sq_le_realEnstrophy
          u i (τ (m n)) (z n))
  have hPhysical :=
    indexedRate_to_physicalClockProduct_of_lowerClock
      (fun n : ℕ =>
        realEnstrophyDensity
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ (m n)) (z n))
      (fun n : ℕ => T - τ (m n)) m c hc hENonneg hIndexed
      hLowerSelected
  exact ⟨i, m, z, hm, hNative, hIndexed, hPhysical⟩

end

end Euclidean
end Bridge
end PrimeTensor
