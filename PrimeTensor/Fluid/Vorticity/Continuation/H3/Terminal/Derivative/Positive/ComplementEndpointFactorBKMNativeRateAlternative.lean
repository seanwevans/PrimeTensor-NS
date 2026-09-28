import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeRawDissipation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeEverySubtail

/-!
# Native rate alternative on every strict terminal subtail

Hypothetical nonextension supplies native quantitative data on each
strict subtail. On a selected native path, either the normalized
vorticity factor has no eventual constant ceiling, or raw H³
dissipation has no subexponential square-root-index ceiling. A ceiling
on both quantities for every possible native witness therefore gives
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Under nonextension, each strict subtail has a native witness for
which either the normalized vorticity factor has no eventual constant
bound or raw dissipation exceeds some square-root exponential rate
arbitrarily far along the native sequence. -/
theorem positiveGrowth_native_vorticity_or_rawDissipation_rate_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hg : ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ p : H3TerminalCurlGradientPair,
        ∃ sCurl sGradient : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            ∃ y : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y ∧
              ((∀ C : ℝ, ¬ ∀ᶠ n : ℕ in atTop,
                  (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C) ∨
                ¬ (∀ c : ℝ, 0 < c →
                  ∀ᶠ n : ℕ in atTop,
                    velocityH3DissipationAt u (τ n) ≤
                      Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2)) := by
  classical
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    positiveGrowth_quantitativeNativeData_on_every_subtail_of_noExtension
      hH3 hNoExtension hClass b hb
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  by_cases hCeiling : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C
  · obtain ⟨C, hC⟩ := hCeiling
    exact Or.inr
      (positiveGrowth_native_rawDissipation_not_subexponential_sqrt
        hH3 hNoExtension hClass hb (hg b hb) hData hC)
  · exact Or.inl (fun C hC => hCeiling ⟨C, hC⟩)

/-- A neutral alternative: continuation or a native rate obstruction
on every strict terminal subtail. -/
theorem smoothContinuationExtension_or_native_rate_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hg : ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ p : H3TerminalCurlGradientPair,
        ∃ sCurl sGradient : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            ∃ y : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y ∧
              ((∀ C : ℝ, ¬ ∀ᶠ n : ℕ in atTop,
                  (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C) ∨
                ¬ (∀ c : ℝ, 0 < c →
                  ∀ᶠ n : ℕ in atTop,
                    velocityH3DissipationAt u (τ n) ≤
                      Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2))) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_native_vorticity_or_rawDissipation_rate_on_every_subtail
        hH3 hExtension hClass hg)

/-- A uniform pair of native witness ceilings rules out nonextension.
The hypotheses apply to every quantitative witness on the chosen
subtail, including the one selected under hypothetical nonextension. -/
theorem smoothContinuationExtension_of_native_vorticity_and_rawDissipation_ceilings
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hCeilings :
      ∀ (p : H3TerminalCurlGradientPair)
        (sCurl sGradient : H3TerminalOrientation)
        (τ : ℕ → ℝ) (y : ℕ → Point3),
        H3TerminalPositiveGrowthQuantitativeNativeData
          u b T p sCurl sGradient τ y →
        (∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
          (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C) ∧
        (∀ c : ℝ, 0 < c →
          ∀ᶠ n : ℕ in atTop,
            velocityH3DissipationAt u (τ n) ≤
              Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  classical
  by_contra hNoExtension
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    positiveGrowth_quantitativeNativeData_on_every_subtail_of_noExtension
      hH3 hNoExtension hClass b hb
  obtain ⟨⟨C, hVorticityCeiling⟩, hDissipationCeiling⟩ :=
    hCeilings p sCurl sGradient τ y hData
  exact (positiveGrowth_native_rawDissipation_not_subexponential_sqrt
    hH3 hNoExtension hClass hb hg hData hVorticityCeiling)
    hDissipationCeiling

end

end Euclidean
end Bridge
end PrimeTensor
