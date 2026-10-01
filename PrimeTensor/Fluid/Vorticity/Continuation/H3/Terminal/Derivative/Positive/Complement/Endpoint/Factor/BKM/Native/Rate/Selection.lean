import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.One.Witness.Rate

/-!
# Selecting a branch of the native endpoint rate alternative

An upper ceiling for every quantitative native witness applies to the
witness chosen under hypothetical nonextension. A subexponential raw
dissipation ceiling selects the divergent normalized vorticity branch;
an eventual normalized vorticity ceiling selects exponential raw
dissipation growth. The ceilings remain explicit assumptions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Every quantitative native witness on a fixed subtail has an
eventual raw dissipation ceiling at every positive square-root
exponential coefficient. -/
def H3TerminalNativeUniformRawSubexponentialCeiling
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) : Prop :=
  ∀ (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ) (y : ℕ → Point3),
    H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y →
    ∀ c : ℝ, 0 < c →
      ∀ᶠ n : ℕ in atTop,
        velocityH3DissipationAt u (τ n) ≤
          Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2

/-- Every quantitative native witness on a fixed subtail has some
eventual constant ceiling for its normalized vorticity factor. The
constant may depend on the witness. -/
def H3TerminalNativeUniformVorticityCeiling
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ) (y : ℕ → Point3),
    H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C

/-- If raw dissipation has a subexponential ceiling on every native
witness of each strict subtail, nonextension forces a native witness
with divergent normalized vorticity on every such subtail. -/
theorem positiveGrowth_native_vorticity_of_uniformRawCeiling_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hg : ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hRawCeiling : ∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalNativeUniformRawSubexponentialCeiling u b T) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ p : H3TerminalCurlGradientPair,
        ∃ sCurl sGradient : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            ∃ y : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y ∧
              (∀ n : ℕ,
                (n : ℝ) <
                  (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1)) ∧
              Tendsto
                (fun n : ℕ =>
                  (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1))
                atTop atTop := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hRate⟩ :=
    positiveGrowth_native_rateAlternative_oneWitness_on_every_subtail
      hH3 hNoExtension hClass hg b hb
  rcases hRate with ⟨hGrowth, hTop⟩ |
      ⟨c, hcPos, hLower⟩
  · exact ⟨p, sCurl, sGradient, τ, y, hData, hGrowth, hTop⟩
  · have hUpper :=
      (hRawCeiling b hb) p sCurl sGradient τ y hData c hcPos
    obtain ⟨n, hnLower, hnUpper⟩ := (hLower.and hUpper).exists
    exact False.elim ((not_lt_of_ge hnUpper) hnLower)

/-- If normalized vorticity has an eventual constant ceiling on every
native witness of each strict subtail, nonextension forces eventual
exponential raw dissipation growth on a native witness of each one. -/
theorem positiveGrowth_native_rawDissipation_of_uniformVorticityCeiling_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hg : ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hVorticityCeiling : ∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalNativeUniformVorticityCeiling u b T g) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ p : H3TerminalCurlGradientPair,
        ∃ sCurl sGradient : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            ∃ y : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y ∧
              ∃ c : ℝ, 0 < c ∧
                ∀ᶠ n : ℕ in atTop,
                  Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
                    velocityH3DissipationAt u (τ n) := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hRate⟩ :=
    positiveGrowth_native_rateAlternative_oneWitness_on_every_subtail
      hH3 hNoExtension hClass hg b hb
  rcases hRate with ⟨_hGrowth, hTop⟩ |
      ⟨c, hcPos, hLower⟩
  · obtain ⟨C, hUpper⟩ :=
      (hVorticityCeiling b hb) p sCurl sGradient τ y hData
    obtain ⟨n, hnUpper, hnLower⟩ :=
      (hUpper.and (hTop.eventually (eventually_gt_atTop C))).exists
    exact False.elim ((not_lt_of_ge hnUpper) hnLower)
  · exact ⟨p, sCurl, sGradient, τ, y,
      hData, c, hcPos, hLower⟩

end

end Euclidean
end Bridge
end PrimeTensor
