import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Fixed.Actual.Vorticity.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Rate.Selection

/-!
# Selecting the fixed actual-vorticity endpoint rate

A subexponential ceiling for raw dissipation on every quantitative
native witness of one strict subtail rules out the dissipation branch.
The remaining witness has one fixed actual vorticity component with
the native-index lower rate. The ceiling is an explicit hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A quantitative native cascade with one fixed actual vorticity
component exceeding `n - 2` at separately selected spatial points. -/
def H3TerminalPositiveGrowthFixedActualVorticityRateData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) : Prop :=
  ∃ p : H3TerminalCurlGradientPair,
    ∃ sCurl sGradient : H3TerminalOrientation,
      ∃ τ : ℕ → ℝ,
        ∃ y : ℕ → Point3,
          ∃ i : Fin 3,
            ∃ z : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y ∧
              (∀ n : ℕ,
                (n : ℝ) - 2 <
                  |h3NativeActualVorticityComponentAt u i (τ n) (z n)|) ∧
              Tendsto
                (fun n : ℕ =>
                  |h3NativeActualVorticityComponentAt u i (τ n) (z n)|)
                atTop atTop

/-- Under nonextension, a raw dissipation ceiling for every native
witness of a chosen strict subtail selects the fixed actual-vorticity
rate on a native witness of that subtail. -/
theorem positiveGrowth_native_fixedActualVorticity_of_uniformRawCeiling_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hRawCeiling :
      H3TerminalNativeUniformRawSubexponentialCeiling u b T) :
    H3TerminalPositiveGrowthFixedActualVorticityRateData u b T := by
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hRate⟩ :=
    positiveGrowth_native_fixedActualVorticity_or_rawDissipation_on_every_subtail
      hH3 hNoExtension hClass b hb
  rcases hRate with ⟨i, z, hBound, hTop⟩ |
      ⟨c, hcPos, hLower⟩
  · exact ⟨p, sCurl, sGradient, τ, y, i, z,
      hData, hBound, hTop⟩
  · have hUpper :=
      hRawCeiling p sCurl sGradient τ y hData c hcPos
    obtain ⟨n, hnLower, hnUpper⟩ := (hLower.and hUpper).exists
    exact False.elim ((not_lt_of_ge hnUpper) hnLower)

/-- A raw dissipation ceiling on all quantitative native witnesses of
each strict subtail selects a fixed actual vorticity component rate
on every one of those subtails under nonextension. -/
theorem positiveGrowth_native_fixedActualVorticity_of_uniformRawCeiling_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hRawCeiling : ∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalNativeUniformRawSubexponentialCeiling u b T) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalPositiveGrowthFixedActualVorticityRateData u b T := by
  intro b hb
  exact positiveGrowth_native_fixedActualVorticity_of_uniformRawCeiling_on_subtail
    hH3 hNoExtension hClass hb (hRawCeiling b hb)

/-- Neutral continuation or a fixed actual vorticity component rate
on each subtail under the stated native raw dissipation ceiling. -/
theorem smoothContinuationExtension_or_native_fixedActualVorticity_of_uniformRawCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hRawCeiling : ∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalNativeUniformRawSubexponentialCeiling u b T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalPositiveGrowthFixedActualVorticityRateData u b T) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_native_fixedActualVorticity_of_uniformRawCeiling_on_every_subtail
        hH3 hExtension hClass hRawCeiling)

end

end Euclidean
end Bridge
end PrimeTensor
