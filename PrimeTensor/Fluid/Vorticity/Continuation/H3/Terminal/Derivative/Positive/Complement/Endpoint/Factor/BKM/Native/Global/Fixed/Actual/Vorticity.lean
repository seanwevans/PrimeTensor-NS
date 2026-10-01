import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Fixed.Actual.Vorticity.Selection
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Subtail

/-!
# One actual vorticity component on all native terminal subtails

Once a fixed actual vorticity component has been selected on one native
endpoint witness, cofinal reindexing places the same component, structural
pair, and orientations on every strict terminal subtail. The spatial points
and times may depend on the subtail.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A single component label, structural pair, and two orientations work
on every strict terminal subtail, with a possibly different native sequence
and actual-vorticity point sequence on each subtail. -/
def H3TerminalPositiveGrowthGlobalFixedActualVorticityRateData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∃ p : H3TerminalCurlGradientPair,
    ∃ sCurl sGradient : H3TerminalOrientation,
      ∃ i : Fin 3,
        ∀ b : ℝ, b ∈ Set.Ioo a T →
          ∃ τ : ℕ → ℝ,
            ∃ y z : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y ∧
              (∀ n : ℕ,
                (n : ℝ) - 2 <
                  |h3NativeActualVorticityComponentAt u i (τ n) (z n)|) ∧
              Tendsto
                (fun n : ℕ =>
                  |h3NativeActualVorticityComponentAt u i (τ n) (z n)|)
                atTop atTop

/-- One fixed-component witness propagates to every strict terminal
subtail with the same component, structural pair, and orientations. -/
theorem positiveGrowth_globalFixedActualVorticity_of_one_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b₀ T : ℝ}
    (hBase : H3TerminalPositiveGrowthFixedActualVorticityRateData u b₀ T) :
    H3TerminalPositiveGrowthGlobalFixedActualVorticityRateData u a T := by
  obtain ⟨p, sCurl, sGradient, τ, y, i, z,
    hData, hBound, hTop⟩ := hBase
  refine ⟨p, sCurl, sGradient, i, ?_⟩
  intro b hb
  obtain ⟨m, hm, hTail⟩ :=
    positiveGrowth_quantitativeNativeData_on_subtail hData hb.2
  have hmTop : Tendsto m atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hm n)
  refine ⟨(fun n => τ (m n)), (fun n => y (m n)),
    (fun n => z (m n)), hTail, ?_, ?_⟩
  · intro n
    have hIndex : (n : ℝ) ≤ (m n : ℝ) := by
      exact_mod_cast hm n
    have hAt := hBound (m n)
    linarith
  · exact hTop.comp hmTop

/-- A raw dissipation ceiling on one chosen strict subtail selects a
component label that subsequently works on every strict terminal subtail. -/
theorem positiveGrowth_globalFixedActualVorticity_of_rawCeiling_on_one_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b₀ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb₀ : b₀ ∈ Set.Ioo a T)
    (hRawCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b₀ T) :
    H3TerminalPositiveGrowthGlobalFixedActualVorticityRateData u a T := by
  exact positiveGrowth_globalFixedActualVorticity_of_one_subtail
    (positiveGrowth_native_fixedActualVorticity_of_uniformRawCeiling_on_subtail
      hH3 hNoExtension hClass hb₀ hRawCeiling)

/-- Under the ceiling on one chosen strict subtail, either the path
continues or a single actual vorticity component has the native lower
rate on every strict terminal subtail. -/
theorem smoothContinuationExtension_or_globalFixedActualVorticity_of_rawCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b₀ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb₀ : b₀ ∈ Set.Ioo a T)
    (hRawCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b₀ T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    H3TerminalPositiveGrowthGlobalFixedActualVorticityRateData u a T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_globalFixedActualVorticity_of_rawCeiling_on_one_subtail
        hH3 hExtension hClass hb₀ hRawCeiling)

end

end Euclidean
end Bridge
end PrimeTensor
