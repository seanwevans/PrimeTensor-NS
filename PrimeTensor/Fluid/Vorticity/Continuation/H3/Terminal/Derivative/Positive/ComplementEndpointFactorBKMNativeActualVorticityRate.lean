import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeEnvelopeMagnitudeRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ActualVorticitySynchronization

/-!
# Actual vorticity in the native endpoint rate alternative

Use the minimal common componentwise vorticity envelope. On its growth
branch, a strict threshold below the minimal envelope is attained by
an actual vorticity component at some spatial point. This point may
differ from the spatial point of the native curl-gradient cascade.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Under nonextension, every strict subtail has a quantitative native
witness with actual vorticity component values above `n - 2` at some
additional spatial points, or eventual exponential raw dissipation
growth on its native times. -/
theorem positiveGrowth_native_actualVorticity_or_rawDissipation_on_every_subtail
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
                  ∀ n : ℕ,
                    ((n : ℝ) - 2 <
                      |realVorticityX
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        (τ n) (z n)|) ∨
                    ((n : ℝ) - 2 <
                      |realVorticityY
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        (τ n) (z n)|) ∨
                    ((n : ℝ) - 2 <
                      |realVorticityZ
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        (τ n) (z n)|)) ∨
                (∃ c : ℝ, 0 < c ∧
                  ∀ᶠ n : ℕ in atTop,
                    Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
                      velocityH3DissipationAt u (τ n))) := by
  classical
  have hg : ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ t : ℝ, t ∈ Set.Ioo b T →
        VorticityEnvelope u (h3MinimalVorticityEnvelopeAt u) t := by
    intro b hb t ht
    have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1) ht.1,
        ht.2⟩
    exact vorticityEnvelope_h3MinimalVorticityEnvelopeAt hH3 ht0
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hRate⟩ :=
    positiveGrowth_native_envelopeMagnitude_or_rawDissipation_on_every_subtail
      (g := h3MinimalVorticityEnvelopeAt u)
      hH3 hNoExtension hClass hg b hb
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hRate with ⟨hLinear, _hMagnitudeTop⟩ | hDissipation
  · have hWitness : ∀ n : ℕ, ∃ z : Point3,
        ((n : ℝ) - 2 <
          |realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ n) z|) ∨
        ((n : ℝ) - 2 <
          |realVorticityY
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ n) z|) ∨
        ((n : ℝ) - 2 <
          |realVorticityZ
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ n) z|) := by
      intro n
      have ht0 : τ n ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1)
          (hData.1 n).1.1,
          (hData.1 n).1.2⟩
      have hMinNonneg :
          0 ≤ h3MinimalVorticityEnvelopeAt u (τ n) :=
        h3MinimalVorticityEnvelopeAt_nonneg_of_h3Path hH3 ht0
      have hLinearN := hLinear n
      rw [abs_of_nonneg hMinNonneg] at hLinearN
      have hThreshold :
          h3MinimalVorticityEnvelopeAt u (τ n) - 1 <
            h3MinimalVorticityEnvelopeAt u (τ n) := by
        linarith
      obtain ⟨z, hz⟩ :=
        exists_actualVorticityComponent_gt_of_lt_h3MinimalVorticityEnvelopeAt
          hThreshold
      refine ⟨z, ?_⟩
      rcases hz with hx | hy | hz
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
    choose z hz using hWitness
    exact Or.inl ⟨z, hz⟩
  · exact Or.inr hDissipation

/-- Neutral continuation or a native witness with actual vorticity
component escape or exponential raw dissipation growth on every
strict terminal subtail. -/
theorem smoothContinuationExtension_or_native_actualVorticityRate_on_every_subtail
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
                  ∀ n : ℕ,
                    ((n : ℝ) - 2 <
                      |realVorticityX
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        (τ n) (z n)|) ∨
                    ((n : ℝ) - 2 <
                      |realVorticityY
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        (τ n) (z n)|) ∨
                    ((n : ℝ) - 2 <
                      |realVorticityZ
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        (τ n) (z n)|)) ∨
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
      (positiveGrowth_native_actualVorticity_or_rawDissipation_on_every_subtail
        hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
