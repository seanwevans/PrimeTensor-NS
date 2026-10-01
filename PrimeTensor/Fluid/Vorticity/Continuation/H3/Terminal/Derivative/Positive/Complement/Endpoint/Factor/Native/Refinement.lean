import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Witness.Cascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Reindex.Cascade

/-!
# Native cascade on a refined endpoint-factor witness

The selected factor-rate witness is cofinal, but its composite index
need not exceed the new counter pointwise. A further cofinal refinement
enforces `n ≤ k (q n)`. The native reindexing theorem then preserves
the complete quantitative positive-growth cascade, while the selected
BKM factor rate and vorticity-envelope limit survive composition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A native quantitative witness with a persistent endpoint-factor
rate and vorticity-envelope divergence on the same extracted indices. -/
def H3TerminalEndpointFactorNativeRefinedWitness
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3)
    (k : ℕ → ℕ)
    (g : ℝ → ℝ) : Prop :=
  ∃ q : ℕ → ℕ,
    Tendsto q atTop atTop ∧
      (∀ n : ℕ, n ≤ k (q n)) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (q n))) (fun n => y (k (q n))) ∧
      Tendsto (fun n : ℕ => |g (τ (k (q n)))|) atTop atTop ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (q n)))|) ^ 2 /
              ((k (q n) : ℝ) + 1))
          atTop atTop ∨
        Tendsto
          (fun n : ℕ =>
            (1 + Real.log (velocityH3EnergyAt u (τ (k (q n))))) ^ 2 /
              ((k (q n) : ℝ) + 1))
          atTop atTop)

private theorem refine_cofinal_index_above_counter
    (m : ℕ → ℕ)
    (hmTop : Tendsto m atTop atTop) :
    ∃ r : ℕ → ℕ,
      Tendsto r atTop atTop ∧
        ∀ n : ℕ, n ≤ m (r n) := by
  classical
  have hChoice :
      ∀ n : ℕ, ∃ N : ℕ, ∀ l : ℕ, N ≤ l → n ≤ m l := by
    intro n
    exact eventually_atTop.1
      (hmTop.eventually (eventually_ge_atTop n))
  choose N hN using hChoice
  let r : ℕ → ℕ := fun n => max n (N n)
  have hrTop : Tendsto r atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro K
    filter_upwards [eventually_ge_atTop K] with n hn
    exact hn.trans (le_max_left n (N n))
  exact ⟨r, hrTop,
    fun n => hN n (r n) (le_max_right n (N n))⟩

private theorem factorWitness_refine_native
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop)
    (hWitness :
      ∃ j : ℕ → ℕ,
        Tendsto j atTop atTop ∧
          Tendsto (fun n : ℕ => |g (τ (k (j n)))|) atTop atTop ∧
          (Tendsto
              (fun n : ℕ =>
                (1 + |g (τ (k (j n)))|) ^ 2 /
                  ((k (j n) : ℝ) + 1))
              atTop atTop ∨
            Tendsto
              (fun n : ℕ =>
                (1 + Real.log (velocityH3EnergyAt u (τ (k (j n))))) ^ 2 /
                  ((k (j n) : ℝ) + 1))
              atTop atTop)) :
    H3TerminalEndpointFactorNativeRefinedWitness
      u b T p sCurl sGradient τ y k g := by
  obtain ⟨j, hjTop, hEnvelope, hRate⟩ := hWitness
  have hComposite :
      Tendsto (fun n : ℕ => k (j n)) atTop atTop :=
    hkTop.comp hjTop
  obtain ⟨r, hrTop, hrIndex⟩ :=
    refine_cofinal_index_above_counter _ hComposite
  let q : ℕ → ℕ := fun n => j (r n)
  have hqTop : Tendsto q atTop atTop :=
    hjTop.comp hrTop
  have hIndex : ∀ n : ℕ, n ≤ k (q n) :=
    fun n => hrIndex n
  have hNative :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (q n))) (fun n => y (k (q n))) :=
    positiveGrowth_quantitativeNativeData_comp_cofinal hData hIndex
  refine ⟨q, hqTop, hIndex, hNative, hEnvelope.comp hrTop, ?_⟩
  rcases hRate with hVorticity | hLogEnergy
  · exact Or.inl (hVorticity.comp hrTop)
  · exact Or.inr (hLogEnergy.comp hrTop)

/-- Gradient-dominant relative escape has a complete native cascade
on a refined persistent BKM factor-rate witness. -/
theorem positiveGrowth_gradientRatioEscape_endpoint_nativeRefinedWitness
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))) :
    H3TerminalEndpointFactorNativeRefinedWitness
      u b T p sCurl sGradient τ y k g := by
  obtain ⟨j, hjTop, _, _, _, hEnvelope, hRate⟩ :=
    positiveGrowth_gradientRatioEscape_endpoint_factorWitnessCascade
      hH3 hNoExtension hClass hb hg hData hCancellation hkTop hRatio
  exact factorWitness_refine_native hData hkTop
    ⟨j, hjTop, hEnvelope, hRate⟩

/-- Curl-dominant relative escape has the same complete native cascade
on a refined persistent BKM factor-rate witness. -/
theorem positiveGrowth_curlRatioEscape_endpoint_nativeRefinedWitness
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))) :
    H3TerminalEndpointFactorNativeRefinedWitness
      u b T p sCurl sGradient τ y k g := by
  obtain ⟨j, hjTop, _, _, _, hEnvelope, hRate⟩ :=
    positiveGrowth_curlRatioEscape_endpoint_factorWitnessCascade
      hH3 hNoExtension hClass hb hg hData hkTop hRatio
  exact factorWitness_refine_native hData hkTop
    ⟨j, hjTop, hEnvelope, hRate⟩

end

end Euclidean
end Bridge
end PrimeTensor
