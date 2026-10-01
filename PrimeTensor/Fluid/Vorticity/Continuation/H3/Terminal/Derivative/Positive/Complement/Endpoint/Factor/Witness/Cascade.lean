import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Branch.Extraction

/-!
# A synchronized witness for the selected endpoint-factor branch

The factor-rate extraction remains cofinal. The native terminal time,
H³ energy, characteristic frequency, and vorticity-envelope limits
therefore pass to the same extracted witness. In the full log-energy
branch, the identity extraction supplies the common index map.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem factorBranch_with_common_index
    (V L : ℕ → ℝ)
    (hBranch :
      (∃ j : ℕ → ℕ,
        Tendsto j atTop atTop ∧
          Tendsto (fun n : ℕ => V (j n)) atTop atTop) ∨
        Tendsto L atTop atTop) :
    ∃ j : ℕ → ℕ,
      Tendsto j atTop atTop ∧
        (Tendsto (fun n : ℕ => V (j n)) atTop atTop ∨
          Tendsto (fun n : ℕ => L (j n)) atTop atTop) := by
  rcases hBranch with ⟨j, hjTop, hV⟩ | hL
  · exact ⟨j, hjTop, Or.inl hV⟩
  · refine ⟨fun n : ℕ => n, ?_, Or.inr ?_⟩
    · refine tendsto_atTop.2 ?_
      intro N
      exact eventually_ge_atTop N
    · exact hL

/-- Gradient-dominant relative escape retains the native scalar and
frequency limits on a cofinal subsequence with one persistent BKM
factor-rate branch. -/
theorem positiveGrowth_gradientRatioEscape_endpoint_factorWitnessCascade
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
    ∃ j : ℕ → ℕ,
      Tendsto j atTop atTop ∧
        Tendsto (fun n : ℕ => τ (k (j n))) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ => velocityH3EnergyAt u (τ (k (j n))))
          atTop atTop ∧
        Tendsto
          (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ (k (j n))))
          atTop atTop ∧
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
            atTop atTop) := by
  have hEnvelope :=
    positiveGrowth_nativeWitness_vorticityEnvelope_atTop
      hH3 hNoExtension hClass hb hg hData
  have hBranch :=
    positiveGrowth_gradientRatioEscape_endpoint_factorBranch
      hH3 hClass hb hg hData hCancellation hkTop hRatio
  obtain ⟨j, hjTop, hRate⟩ :=
    factorBranch_with_common_index
      (fun n => (1 + |g (τ (k n))|) ^ 2 / ((k n : ℝ) + 1))
      (fun n =>
        (1 + Real.log (velocityH3EnergyAt u (τ (k n)))) ^ 2 /
          ((k n : ℝ) + 1))
      hBranch
  obtain ⟨_, hTau, hEnergy, _, _, hFrequency, _, _, _⟩ := hData
  have hCombined : Tendsto (fun n : ℕ => k (j n)) atTop atTop :=
    hkTop.comp hjTop
  exact ⟨j, hjTop, hTau.comp hCombined, hEnergy.comp hCombined,
    hFrequency.comp hCombined, hEnvelope.comp hCombined, hRate⟩

/-- Curl-dominant relative escape retains the same native scalar and
frequency limits on its persistent endpoint-factor branch. -/
theorem positiveGrowth_curlRatioEscape_endpoint_factorWitnessCascade
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
    ∃ j : ℕ → ℕ,
      Tendsto j atTop atTop ∧
        Tendsto (fun n : ℕ => τ (k (j n))) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ => velocityH3EnergyAt u (τ (k (j n))))
          atTop atTop ∧
        Tendsto
          (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ (k (j n))))
          atTop atTop ∧
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
            atTop atTop) := by
  have hEnvelope :=
    positiveGrowth_nativeWitness_vorticityEnvelope_atTop
      hH3 hNoExtension hClass hb hg hData
  have hBranch :=
    positiveGrowth_curlRatioEscape_endpoint_factorBranch
      hH3 hClass hb hg hData hkTop hRatio
  obtain ⟨j, hjTop, hRate⟩ :=
    factorBranch_with_common_index
      (fun n => (1 + |g (τ (k n))|) ^ 2 / ((k n : ℝ) + 1))
      (fun n =>
        (1 + Real.log (velocityH3EnergyAt u (τ (k n)))) ^ 2 /
          ((k n : ℝ) + 1))
      hBranch
  obtain ⟨_, hTau, hEnergy, _, _, hFrequency, _, _, _⟩ := hData
  have hCombined : Tendsto (fun n : ℕ => k (j n)) atTop atTop :=
    hkTop.comp hjTop
  exact ⟨j, hjTop, hTau.comp hCombined, hEnergy.comp hCombined,
    hFrequency.comp hCombined, hEnvelope.comp hCombined, hRate⟩

end

end Euclidean
end Bridge
end PrimeTensor
