import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Native.Refinement

/-!
# Relative escape on the refined endpoint-factor witness

The native endpoint-factor witness already satisfies the quantitative
index bound. A final cofinal refinement also makes its extraction map
exceed the new counter. Thus the relative-ratio escape inequality passes
to the same witness as the full native cascade and the selected BKM
factor rate, in either curl-gradient orientation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A quantitative native witness carrying both a persistent BKM
factor rate and the relative-ratio lower bound at the new counter. -/
def H3TerminalEndpointFactorRelativeRefinedWitness
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3)
    (k : ℕ → ℕ)
    (g : ℝ → ℝ)
    (ratio : ℕ → ℝ) : Prop :=
  ∃ l : ℕ → ℕ,
    Tendsto l atTop atTop ∧
      (∀ n : ℕ, n ≤ l n ∧ n ≤ k (l n)) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l n))) (fun n => y (k (l n))) ∧
      Tendsto (fun n : ℕ => |g (τ (k (l n)))|) atTop atTop ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (l n)))|) ^ 2 /
              ((k (l n) : ℝ) + 1))
          atTop atTop ∨
        Tendsto
          (fun n : ℕ =>
            (1 + Real.log (velocityH3EnergyAt u (τ (k (l n))))) ^ 2 /
              ((k (l n) : ℝ) + 1))
          atTop atTop) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l n))

private theorem endpointFactorNative_refine_relative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    {ratio : ℕ → ℝ}
    (hBase :
      H3TerminalEndpointFactorNativeRefinedWitness
        u b T p sCurl sGradient τ y k g)
    (hRatio : ∀ n : ℕ, (n : ℝ) + 1 < ratio n) :
    H3TerminalEndpointFactorRelativeRefinedWitness
      u b T p sCurl sGradient τ y k g ratio := by
  classical
  obtain ⟨q, hqTop, hOriginalIndex, hNative, hEnvelope, hRate⟩ := hBase
  have hChoice :
      ∀ n : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → n ≤ q m := by
    intro n
    exact eventually_atTop.1
      (hqTop.eventually (eventually_ge_atTop n))
  choose N hN using hChoice
  let s : ℕ → ℕ := fun n => max n (N n)
  have hsIndex : ∀ n : ℕ, n ≤ s n :=
    fun n => le_max_left n (N n)
  have hsTop : Tendsto s atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro K
    filter_upwards [eventually_ge_atTop K] with n hn
    exact hn.trans (hsIndex n)
  let l : ℕ → ℕ := fun n => q (s n)
  have hlTop : Tendsto l atTop atTop :=
    hqTop.comp hsTop
  have hlIndex : ∀ n : ℕ, n ≤ l n :=
    fun n => hN n (s n) (le_max_right n (N n))
  have hkIndex : ∀ n : ℕ, n ≤ k (l n) := by
    intro n
    exact (hsIndex n).trans (hOriginalIndex (s n))
  have hNative' :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l n))) (fun n => y (k (l n))) :=
    positiveGrowth_quantitativeNativeData_comp_cofinal hNative hsIndex
  have hRatio' : ∀ n : ℕ, (n : ℝ) + 1 < ratio (l n) := by
    intro n
    have hCast : (n : ℝ) ≤ (l n : ℝ) := by
      exact_mod_cast (hlIndex n)
    exact lt_of_le_of_lt (by linarith) (hRatio (l n))
  refine ⟨l, hlTop, (fun n => ⟨hlIndex n, hkIndex n⟩),
    hNative', hEnvelope.comp hsTop, ?_, hRatio'⟩
  rcases hRate with hVorticity | hLogEnergy
  · exact Or.inl (hVorticity.comp hsTop)
  · exact Or.inr (hLogEnergy.comp hsTop)

/-- Gradient-dominant escape retains its ratio lower bound after
refining the persistent endpoint-factor witness. -/
theorem positiveGrowth_gradientRatioEscape_endpoint_relativeRefinedWitness
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
    H3TerminalEndpointFactorRelativeRefinedWitness
      u b T p sCurl sGradient τ y k g
        (fun n =>
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))) := by
  exact endpointFactorNative_refine_relative
    (positiveGrowth_gradientRatioEscape_endpoint_nativeRefinedWitness
      hH3 hNoExtension hClass hb hg hData hCancellation hkTop hRatio)
    hRatio

/-- Curl-dominant escape retains its ratio lower bound on the same
refined native and persistent endpoint-factor witness. -/
theorem positiveGrowth_curlRatioEscape_endpoint_relativeRefinedWitness
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
    H3TerminalEndpointFactorRelativeRefinedWitness
      u b T p sCurl sGradient τ y k g
        (fun n =>
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))) := by
  exact endpointFactorNative_refine_relative
    (positiveGrowth_curlRatioEscape_endpoint_nativeRefinedWitness
      hH3 hNoExtension hClass hb hg hData hkTop hRatio)
    hRatio

end

end Euclidean
end Bridge
end PrimeTensor
