import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMIntrinsicLogRate

/-!
# Intrinsic frequency-log ceiling obstruction

Under hypothetical nonextension, polynomial normalized energy growth and a
bounded normalized vorticity factor force the intrinsic characteristic-
frequency logarithm above every original-index power on one relative
positive-growth witness. An eventual polynomial ceiling for that logarithm
on the original sequence therefore excludes this witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Joint polynomial energy-growth and intrinsic frequency-log ceilings,
together with a bounded normalized vorticity factor, exclude the
relative positive-growth witness in the nonextension regime. -/
theorem endpointFactor_noRelativeRefinedWitness_of_intrinsicLogCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    {ratio : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B)
    (F : ℝ) (frequencyDegree : ℕ)
    (hFrequencyLogCeiling : ∀ᶠ i : ℕ in atTop,
      1 + Real.log (h3TopCharacteristicFrequencyAt u (τ i)) ≤
        F * (((i : ℝ) + 1) ^ frequencyDegree)) :
    ¬ H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio := by
  intro hWitness
  obtain ⟨l, r, hIndex, _, _, _, _, _, _, _, _, hLogRate⟩ :=
    endpointFactor_relativeRefinedWitness_intrinsicLogSuperpolynomial
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  have hBound := hIndex.eventually hFrequencyLogCeiling
  have hLarge := (hLogRate frequencyDegree).eventually
    (eventually_gt_atTop F)
  obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
  have hScale : 0 < ((k (l (r n)) : ℝ) + 1) ^ frequencyDegree := by
    positivity
  have hnStrict :
      F * (((k (l (r n)) : ℝ) + 1) ^ frequencyDegree) <
        1 + Real.log
          (h3TopCharacteristicFrequencyAt u (τ (k (l (r n))))) :=
    (lt_div_iff₀ hScale).mp hnLarge
  exact (not_lt_of_ge hnBound) hnStrict

end

end Euclidean
end Bridge
end PrimeTensor
