import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Rate.Alternative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Reindex.Cascade

/-!
# Extracting the native endpoint rate alternative

An unbounded normalized vorticity factor has a cofinal extraction on
which it grows beyond each new index. The quantitative native cascade
survives that extraction. If the factor instead has an eventual constant
ceiling, raw dissipation exceeds a fixed exponential square-root-index
rate eventually on the original native sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A sequence without any eventual constant upper bound can be
sampled cofinally above each new index. -/
theorem cofinal_extraction_of_no_eventual_real_ceiling
    (R : ℕ → ℝ)
    (hUnbounded : ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, R n ≤ C) :
    ∃ k : ℕ → ℕ,
      (∀ n : ℕ, n ≤ k n ∧ (n : ℝ) < R (k n)) ∧
      Tendsto (fun n : ℕ => R (k n)) atTop atTop := by
  classical
  have hCofinal : ∀ N : ℕ,
      ∃ m : ℕ, N ≤ m ∧ (N : ℝ) < R m := by
    intro N
    by_contra hNo
    apply hUnbounded
    refine ⟨(N : ℝ), ?_⟩
    filter_upwards [eventually_ge_atTop N] with m hm
    by_contra hGt
    exact hNo ⟨m, hm, lt_of_not_ge hGt⟩
  choose k hk using hCofinal
  have hGrowth : ∀ n : ℕ, (n : ℝ) < R (k n) :=
    fun n => (hk n).2
  refine ⟨k, hk, ?_⟩
  refine tendsto_atTop.2 ?_
  intro C
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt C
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact (le_of_lt hN).trans (hCast.trans (le_of_lt (hGrowth n)))

/-- On every strict terminal subtail of a nonextending path, either a
cofinal native extraction has divergent normalized vorticity, or the
original native witness has an eventual raw dissipation exponential
square-root-index lower bound. The vorticity ratio in the first branch
uses the original index `k n` in its denominator. -/
theorem positiveGrowth_native_extractedVorticity_or_rawDissipation_on_every_subtail
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
                      (1 + |g (τ (k n))|) ^ 2 / ((k n : ℝ) + 1)) ∧
                  Tendsto
                    (fun n : ℕ =>
                      (1 + |g (τ (k n))|) ^ 2 / ((k n : ℝ) + 1))
                    atTop atTop) ∨
                (∃ c : ℝ, 0 < c ∧
                  ∀ᶠ n : ℕ in atTop,
                    Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
                      velocityH3DissipationAt u (τ n))) := by
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
      (positiveGrowth_native_rawDissipation_exponential_sqrt_lower
        hH3 hNoExtension hClass hb (hg b hb) hData hC)
  · obtain ⟨k, hk, hTop⟩ :=
      cofinal_extraction_of_no_eventual_real_ceiling
        (fun n => (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1))
        hCeiling
    exact Or.inl ⟨k, (fun n => (hk n).1),
      positiveGrowth_quantitativeNativeData_comp_cofinal
        hData (fun n => (hk n).1),
      (fun n => (hk n).2), hTop⟩

/-- Neutral continuation or an extracted vorticity growth branch or an
eventual raw dissipation growth branch on every strict subtail. -/
theorem smoothContinuationExtension_or_native_extractedRate_on_every_subtail
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
                      (1 + |g (τ (k n))|) ^ 2 / ((k n : ℝ) + 1)) ∧
                  Tendsto
                    (fun n : ℕ =>
                      (1 + |g (τ (k n))|) ^ 2 / ((k n : ℝ) + 1))
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
      (positiveGrowth_native_extractedVorticity_or_rawDissipation_on_every_subtail
        hH3 hExtension hClass hg)

end

end Euclidean
end Bridge
end PrimeTensor
