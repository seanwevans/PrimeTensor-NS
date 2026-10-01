import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Envelope.Factor.Rate

/-!
# Magnitude of the native endpoint envelope

The squared envelope-factor bound implies a linear lower bound for the
nonnegative envelope magnitude along the same native time sequence.
This gives a direct alternative between growth of the chosen envelope
and eventual exponential growth of raw H³ dissipation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Quadratic growth of the squared envelope factor yields a linear
bound and divergence of the absolute envelope magnitude. -/
theorem native_envelopeFactor_growth_to_magnitude
    (g : ℝ → ℝ) (τ : ℕ → ℝ)
    (hQuadratic : ∀ n : ℕ,
      (n : ℝ) * ((n : ℝ) + 1) <
        (1 + |g (τ n)|) ^ 2) :
    (∀ n : ℕ, (n : ℝ) < 1 + |g (τ n)|) ∧
    Tendsto (fun n : ℕ => |g (τ n)|) atTop atTop := by
  have hLinear : ∀ n : ℕ,
      (n : ℝ) < 1 + |g (τ n)| := by
    intro n
    have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hFactorNonneg : 0 ≤ 1 + |g (τ n)| := by positivity
    have hSquareLe :
        (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by
      nlinarith
    have hSquare :
        (n : ℝ) ^ 2 < (1 + |g (τ n)|) ^ 2 :=
      lt_of_le_of_lt hSquareLe (hQuadratic n)
    exact (sq_lt_sq₀ hnNonneg hFactorNonneg).1 hSquare
  refine ⟨hLinear, ?_⟩
  refine tendsto_atTop.2 ?_
  intro C
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (C + 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith [hLinear n]

/-- Under nonextension, each strict subtail has one quantitative native
witness with a linearly escaping envelope magnitude, or eventual
exponential raw H³ dissipation growth. -/
theorem positiveGrowth_native_envelopeMagnitude_or_rawDissipation_on_every_subtail
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
                  (n : ℝ) < 1 + |g (τ n)|) ∧
                Tendsto (fun n : ℕ => |g (τ n)|) atTop atTop) ∨
                (∃ c : ℝ, 0 < c ∧
                  ∀ᶠ n : ℕ in atTop,
                    Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
                      velocityH3DissipationAt u (τ n))) := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hRate⟩ :=
    positiveGrowth_native_envelopeFactor_or_rawDissipation_on_every_subtail
      hH3 hNoExtension hClass hg b hb
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hRate with ⟨hQuadratic, _hFactorTop⟩ | hDissipation
  · exact Or.inl
      (native_envelopeFactor_growth_to_magnitude g τ hQuadratic)
  · exact Or.inr hDissipation

/-- Neutral continuation or an envelope-magnitude or raw dissipation
rate witness on every strict terminal subtail. -/
theorem smoothContinuationExtension_or_native_envelopeMagnitudeRate_on_every_subtail
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
                  (n : ℝ) < 1 + |g (τ n)|) ∧
                Tendsto (fun n : ℕ => |g (τ n)|) atTop atTop) ∨
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
      (positiveGrowth_native_envelopeMagnitude_or_rawDissipation_on_every_subtail
        hH3 hExtension hClass hg)

end

end Euclidean
end Bridge
end PrimeTensor
