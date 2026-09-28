import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeRateExtraction

/-!
# Native-index form of the extracted endpoint rate

The extracted vorticity rate initially uses the original index `k n`
in its denominator. Since `n ≤ k n`, replacing that denominator by the
new native index `n` only increases the nonnegative ratio. The full
native cascade thus has a divergent normalized vorticity factor in its
own indexing, or the original witness has eventual exponential raw
dissipation growth.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Growth of the original-index normalized vorticity factor transfers
to the native normalization of the reindexed sequence. -/
theorem native_vorticity_rate_reindexed_to_new_index
    (g : ℝ → ℝ) (τ : ℕ → ℝ) (k : ℕ → ℕ)
    (hk : ∀ n : ℕ, n ≤ k n)
    (hGrowth : ∀ n : ℕ,
      (n : ℝ) <
        (1 + |g (τ (k n))|) ^ 2 / ((k n : ℝ) + 1)) :
    (∀ n : ℕ,
      (n : ℝ) <
        (1 + |g (τ (k n))|) ^ 2 / ((n : ℝ) + 1)) ∧
    Tendsto
      (fun n : ℕ =>
        (1 + |g (τ (k n))|) ^ 2 / ((n : ℝ) + 1))
      atTop atTop := by
  have hNewGrowth : ∀ n : ℕ,
      (n : ℝ) <
        (1 + |g (τ (k n))|) ^ 2 / ((n : ℝ) + 1) := by
    intro n
    have hCast : (n : ℝ) ≤ (k n : ℝ) := by
      exact_mod_cast hk n
    have hDen : (n : ℝ) + 1 ≤ (k n : ℝ) + 1 := by
      linarith
    have hInv :
        (1 : ℝ) / ((k n : ℝ) + 1) ≤
          1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hDen
    have hNum : 0 ≤ (1 + |g (τ (k n))|) ^ 2 :=
      sq_nonneg _
    have hRatio :
        (1 + |g (τ (k n))|) ^ 2 / ((k n : ℝ) + 1) ≤
          (1 + |g (τ (k n))|) ^ 2 / ((n : ℝ) + 1) := by
      simpa only [div_eq_mul_inv, one_div, one_mul] using
        (mul_le_mul_of_nonneg_left hInv hNum)
    exact (hGrowth n).trans_le hRatio
  refine ⟨hNewGrowth, ?_⟩
  refine tendsto_atTop.2 ?_
  intro C
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt C
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact (le_of_lt hN).trans (hCast.trans (le_of_lt (hNewGrowth n)))

/-- The native vorticity branch is indexed by the extracted native
witness itself; its ratio exceeds every index and tends to infinity. -/
theorem positiveGrowth_native_reindexedVorticity_or_rawDissipation_on_every_subtail
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
              ((∃ k : ℕ → ℕ,
                  (∀ n : ℕ, n ≤ k n) ∧
                  H3TerminalPositiveGrowthQuantitativeNativeData
                    u b T p sCurl sGradient
                      (fun n => τ (k n)) (fun n => y (k n)) ∧
                  (∀ n : ℕ,
                    (n : ℝ) <
                      (1 + |g (τ (k n))|) ^ 2 / ((n : ℝ) + 1)) ∧
                  Tendsto
                    (fun n : ℕ =>
                      (1 + |g (τ (k n))|) ^ 2 / ((n : ℝ) + 1))
                    atTop atTop) ∨
                (∃ c : ℝ, 0 < c ∧
                  ∀ᶠ n : ℕ in atTop,
                    Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
                      velocityH3DissipationAt u (τ n))) := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hRate⟩ :=
    positiveGrowth_native_extractedVorticity_or_rawDissipation_on_every_subtail
      hH3 hNoExtension hClass hg b hb
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hRate with ⟨k, hk, hNative, hGrowth, _hTop⟩ | hDissipation
  · obtain ⟨hNewGrowth, hNewTop⟩ :=
      native_vorticity_rate_reindexed_to_new_index g τ k hk hGrowth
    exact Or.inl ⟨k, hk, hNative, hNewGrowth, hNewTop⟩
  · exact Or.inr hDissipation

/-- Neutral continuation or a native-index vorticity divergence or
eventual exponential raw dissipation growth on each strict subtail. -/
theorem smoothContinuationExtension_or_native_reindexedRate_on_every_subtail
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
              ((∃ k : ℕ → ℕ,
                  (∀ n : ℕ, n ≤ k n) ∧
                  H3TerminalPositiveGrowthQuantitativeNativeData
                    u b T p sCurl sGradient
                      (fun n => τ (k n)) (fun n => y (k n)) ∧
                  (∀ n : ℕ,
                    (n : ℝ) <
                      (1 + |g (τ (k n))|) ^ 2 / ((n : ℝ) + 1)) ∧
                  Tendsto
                    (fun n : ℕ =>
                      (1 + |g (τ (k n))|) ^ 2 / ((n : ℝ) + 1))
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
      (positiveGrowth_native_reindexedVorticity_or_rawDissipation_on_every_subtail
        hH3 hExtension hClass hg)

end

end Euclidean
end Bridge
end PrimeTensor
