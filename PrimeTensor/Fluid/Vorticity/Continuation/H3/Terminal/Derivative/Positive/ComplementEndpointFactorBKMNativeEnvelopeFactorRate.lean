import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeRateSelection

/-!
# Direct native endpoint envelope-factor rate

The normalized vorticity branch exceeds each native index. Multiplying
by its positive denominator yields a quadratic lower bound for the
squared envelope factor itself. The same native witness still carries
the alternative eventual exponential growth of raw H³ dissipation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Native-index growth of the normalized envelope factor gives a
quadratic pointwise lower bound and divergence of its numerator. -/
theorem native_normalizedVorticity_growth_to_envelopeFactor
    (g : ℝ → ℝ) (τ : ℕ → ℝ)
    (hGrowth : ∀ n : ℕ,
      (n : ℝ) <
        (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1)) :
    (∀ n : ℕ,
      (n : ℝ) * ((n : ℝ) + 1) < (1 + |g (τ n)|) ^ 2) ∧
    Tendsto (fun n : ℕ => (1 + |g (τ n)|) ^ 2)
      atTop atTop := by
  have hQuadratic : ∀ n : ℕ,
      (n : ℝ) * ((n : ℝ) + 1) <
        (1 + |g (τ n)|) ^ 2 := by
    intro n
    have hDen : 0 < (n : ℝ) + 1 := by positivity
    exact (lt_div_iff₀ hDen).mp (hGrowth n)
  refine ⟨hQuadratic, ?_⟩
  refine tendsto_atTop.2 ?_
  intro C
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt C
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hProduct : (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ)]
  exact (le_of_lt hN).trans
    (hCast.trans (hProduct.trans (le_of_lt (hQuadratic n))))

/-- Under nonextension, every strict subtail has one native cascade
whose envelope factor grows above the quadratic index scale, or whose
raw H³ dissipation eventually exceeds a square-root exponential. -/
theorem positiveGrowth_native_envelopeFactor_or_rawDissipation_on_every_subtail
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
              (((∀ n : ℕ,
                  (n : ℝ) * ((n : ℝ) + 1) <
                    (1 + |g (τ n)|) ^ 2) ∧
                Tendsto (fun n : ℕ => (1 + |g (τ n)|) ^ 2)
                  atTop atTop) ∨
                (∃ c : ℝ, 0 < c ∧
                  ∀ᶠ n : ℕ in atTop,
                    Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
                      velocityH3DissipationAt u (τ n))) := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hRate⟩ :=
    positiveGrowth_native_rateAlternative_oneWitness_on_every_subtail
      hH3 hNoExtension hClass hg b hb
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hRate with ⟨hGrowth, _hTop⟩ | hDissipation
  · exact Or.inl
      (native_normalizedVorticity_growth_to_envelopeFactor
        g τ hGrowth)
  · exact Or.inr hDissipation

/-- Neutral continuation or a direct envelope-factor or raw
dissipation rate witness on every strict terminal subtail. -/
theorem smoothContinuationExtension_or_native_envelopeFactorRate_on_every_subtail
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
              (((∀ n : ℕ,
                  (n : ℝ) * ((n : ℝ) + 1) <
                    (1 + |g (τ n)|) ^ 2) ∧
                Tendsto (fun n : ℕ => (1 + |g (τ n)|) ^ 2)
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
      (positiveGrowth_native_envelopeFactor_or_rawDissipation_on_every_subtail
        hH3 hExtension hClass hg)

end

end Euclidean
end Bridge
end PrimeTensor
