import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeUnanchoredDissipation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMRawExcessExponential

/-!
# Raw dissipation cost of a native endpoint witness

Since H³ energy is at least one, normalized dissipation is bounded by
raw full H³ dissipation. The unanchored exponential rate therefore
transfers without changing the native witness. In particular, an upper
ceiling at every positive square-root exponential coefficient is
incompatible with this nonextension witness and vorticity ceiling.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Raw full H³ dissipation retains the native exponential
square-root-index lower bound under the normalized vorticity ceiling. -/
theorem positiveGrowth_native_rawDissipation_exponential_sqrt_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    {g : ℝ → ℝ} {C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hVorticityCeiling : ∀ᶠ n : ℕ in atTop,
      (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
          velocityH3DissipationAt u (τ n) := by
  obtain ⟨c, hcPos, hNormalized⟩ :=
    positiveGrowth_native_dissipationRatio_unanchored_exponential_sqrt_lower
      hH3 hNoExtension hClass hb hg hData hVorticityCeiling
  refine ⟨c, hcPos, ?_⟩
  filter_upwards [hNormalized] with n hn
  have hEnergyOne : 1 ≤ velocityH3EnergyAt u (τ n) :=
    one_le_velocityH3EnergyAt u (τ n)
  have hDNonneg : 0 ≤ velocityH3DissipationAt u (τ n) :=
    velocityH3DissipationAt_nonneg u (τ n)
  have hNormalizedLeRaw :
      velocityH3DissipationAt u (τ n) /
          velocityH3EnergyAt u (τ n) ≤
        velocityH3DissipationAt u (τ n) :=
    dissipation_div_energy_le_raw_of_energy_one _ _ hDNonneg hEnergyOne
  exact hn.trans_le hNormalizedLeRaw

/-- A native nonextension witness under the vorticity ceiling cannot
have an eventual raw dissipation upper bound at every positive
exponential square-root-index coefficient. -/
theorem positiveGrowth_native_rawDissipation_not_subexponential_sqrt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    {g : ℝ → ℝ} {C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hVorticityCeiling : ∀ᶠ n : ℕ in atTop,
      (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C) :
    ¬ (∀ c : ℝ, 0 < c →
      ∀ᶠ n : ℕ in atTop,
        velocityH3DissipationAt u (τ n) ≤
          Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2) := by
  intro hUpper
  obtain ⟨c, hcPos, hLower⟩ :=
    positiveGrowth_native_rawDissipation_exponential_sqrt_lower
      hH3 hNoExtension hClass hb hg hData hVorticityCeiling
  obtain ⟨n, hnLower, hnUpper⟩ :=
    (hLower.and (hUpper c hcPos)).exists
  exact (not_lt_of_ge hnUpper) hnLower

end

end Euclidean
end Bridge
end PrimeTensor
