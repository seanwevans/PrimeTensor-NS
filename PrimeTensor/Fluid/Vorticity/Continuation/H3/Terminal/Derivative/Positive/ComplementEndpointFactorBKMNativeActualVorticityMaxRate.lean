import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeActualVorticityRate

/-!
# Quantitative maximum of the actual native vorticity components

The component that exceeds the native index may change from one time
to the next. Taking the maximum of the three actual component
magnitudes at the separately selected spatial points keeps the
pointwise rate and gives a divergent scalar sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The largest actual vorticity component magnitude at one space-time
point of the logged velocity. -/
def h3NativeActualVorticityComponentMaxAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (x : Point3) : ℝ :=
  max
    |realVorticityX (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x|
    (max
      |realVorticityY (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x|
      |realVorticityZ (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x|)

/-- A pointwise lower bound for one of the three components transfers
to their maximum and makes that maximum diverge. -/
theorem native_actualVorticity_componentRate_to_maxRate
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
    (∀ n : ℕ,
      (n : ℝ) - 2 <
        h3NativeActualVorticityComponentMaxAt u (τ n) (z n)) ∧
    Tendsto
      (fun n : ℕ => h3NativeActualVorticityComponentMaxAt u (τ n) (z n))
      atTop atTop := by
  have hMax : ∀ n : ℕ,
      (n : ℝ) - 2 <
        h3NativeActualVorticityComponentMaxAt u (τ n) (z n) := by
    intro n
    dsimp only [h3NativeActualVorticityComponentMaxAt]
    rcases hComponent n with hx | hy | hz
    · exact lt_of_lt_of_le hx (le_max_left _ _)
    · exact lt_of_lt_of_le hy
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact lt_of_lt_of_le hz
        (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨hMax, ?_⟩
  refine tendsto_atTop.2 ?_
  intro C
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (C + 2)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith [hMax n]

/-- Under nonextension, every strict subtail has a native quantitative
witness with a linearly growing actual vorticity component maximum at
selected spatial points, or eventual exponential raw dissipation
growth on its native times. -/
theorem positiveGrowth_native_actualVorticityMax_or_rawDissipation_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ p : H3TerminalCurlGradientPair,
        ∃ sCurl sGradient : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            ∃ y : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y ∧
              ((∃ z : ℕ → Point3,
                  (∀ n : ℕ,
                    (n : ℝ) - 2 <
                      h3NativeActualVorticityComponentMaxAt u (τ n) (z n)) ∧
                  Tendsto
                    (fun n : ℕ =>
                      h3NativeActualVorticityComponentMaxAt u (τ n) (z n))
                    atTop atTop) ∨
                (∃ c : ℝ, 0 < c ∧
                  ∀ᶠ n : ℕ in atTop,
                    Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
                      velocityH3DissipationAt u (τ n))) := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hRate⟩ :=
    positiveGrowth_native_actualVorticity_or_rawDissipation_on_every_subtail
      hH3 hNoExtension hClass b hb
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hRate with ⟨z, hComponent⟩ | hDissipation
  · obtain ⟨hMax, hMaxTop⟩ :=
      native_actualVorticity_componentRate_to_maxRate u τ z hComponent
    exact Or.inl ⟨z, hMax, hMaxTop⟩
  · exact Or.inr hDissipation

/-- Neutral continuation or actual vorticity maximum growth or raw
dissipation growth on every strict terminal subtail. -/
theorem smoothContinuationExtension_or_native_actualVorticityMaxRate_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ p : H3TerminalCurlGradientPair,
        ∃ sCurl sGradient : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            ∃ y : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y ∧
              ((∃ z : ℕ → Point3,
                  (∀ n : ℕ,
                    (n : ℝ) - 2 <
                      h3NativeActualVorticityComponentMaxAt u (τ n) (z n)) ∧
                  Tendsto
                    (fun n : ℕ =>
                      h3NativeActualVorticityComponentMaxAt u (τ n) (z n))
                    atTop atTop) ∨
                (∃ c : ℝ, 0 < c ∧
                  ∀ᶠ n : ℕ in atTop,
                    Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
                      velocityH3DissipationAt u (τ n)))) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_native_actualVorticityMax_or_rawDissipation_on_every_subtail
        hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
