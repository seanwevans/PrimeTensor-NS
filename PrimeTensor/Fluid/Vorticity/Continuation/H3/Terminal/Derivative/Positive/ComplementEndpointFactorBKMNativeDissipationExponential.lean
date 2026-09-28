import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFrequencyExponential
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorFrequencyDissipationBarrier

/-!
# Native exponential frequency rate forces normalized dissipation

Under hypothetical nonextension and a normalized vorticity ceiling,
the intrinsic frequency exceeds one fixed exponential square-root-index
scale on every quantitative native witness. The existing tail comparison
controls its square by anchored full H³ dissipation divided by H³ energy.
This statement does not select a relative-ratio or physical corridor branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The squared exponential square-root-index scale is eventually below
anchored normalized full H³ dissipation on the unchanged native witness. -/
theorem positiveGrowth_native_dissipationRatio_exponential_sqrt_lower
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
          (4 + 3 * velocityH3Energy0At u b) *
            (velocityH3DissipationAt u (τ n) /
              velocityH3EnergyAt u (τ n)) := by
  obtain ⟨c, hcPos, hFrequency⟩ :=
    positiveGrowth_native_intrinsicFrequency_exponential_sqrt_lower
      hH3 hNoExtension hClass hb hg hData hVorticityCeiling
  have hFrequencySq :=
    positiveGrowth_nativeWitness_frequencySq_le_dissipationRatio
      hH3 hNoExtension hClass hb hData
  refine ⟨c, hcPos, ?_⟩
  filter_upwards [hFrequency, hFrequencySq] with n hn hnSq
  have hExpNonneg :
      0 ≤ Real.exp (c * Real.sqrt ((n : ℝ) + 1)) :=
    le_of_lt (Real.exp_pos _)
  have hSquared :
      Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
        h3TopCharacteristicFrequencyAt u (τ n) ^ 2 :=
    pow_lt_pow_left₀ hn hExpNonneg (by norm_num)
  exact hSquared.trans_le hnSq

end

end Euclidean
end Bridge
end PrimeTensor
