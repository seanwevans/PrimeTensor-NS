import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Dissipation.Corridor

/-!
# Polynomial physical-rate ceiling on the positive-growth witness

An eventual polynomial ceiling on the smallest of normalized dissipation,
transport excess, and adverse transport excludes the physical branch when
normalized energy growth also has a polynomial ceiling.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Three superpolynomial rates force their minimum above every fixed
polynomial scale on the same sequence. -/
theorem physicalRates_superpolynomial_min
    (D Q A : ℕ → ℝ) (scale : ℕ → ℕ → ℝ)
    (hScale : ∀ degree n, 0 < scale degree n)
    (hD : ∀ degree, Tendsto (fun n => D n / scale degree n) atTop atTop)
    (hQ : ∀ degree, Tendsto (fun n => Q n / scale degree n) atTop atTop)
    (hA : ∀ degree, Tendsto (fun n => A n / scale degree n) atTop atTop)
    (degree : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      B * scale degree n < min (D n) (min (Q n) (A n)) := by
  have hd := (hD degree).eventually (eventually_gt_atTop B)
  have hq := (hQ degree).eventually (eventually_gt_atTop B)
  have ha := (hA degree).eventually (eventually_gt_atTop B)
  filter_upwards [hd, hq, ha] with n hnD hnQ hnA
  have hnD' : B * scale degree n < D n :=
    (lt_div_iff₀ (hScale degree n)).mp hnD
  have hnQ' : B * scale degree n < Q n :=
    (lt_div_iff₀ (hScale degree n)).mp hnQ
  have hnA' : B * scale degree n < A n :=
    (lt_div_iff₀ (hScale degree n)).mp hnA
  exact lt_min hnD' (lt_min hnQ' hnA')

/-- Polynomial bounds on normalized energy growth and on the smallest
physical rate force normalized vorticity escape along a common native witness. -/
theorem endpointFactor_relativeRefinedWitness_vorticity_of_polynomialPhysicalCeiling
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
    (hWitness :
      H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio)
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ) (rateDegree : ℕ)
    (hPhysicalCeiling : ∀ᶠ i : ℕ in atTop,
      min
          (velocityH3DissipationAt u (τ i) /
            velocityH3EnergyAt u (τ i))
          (min (h3PathTransportExcessRate u (τ i))
            ((-velocityH3TransportDerivativeAt u (τ i)) /
              velocityH3EnergyAt u (τ i))) ≤
        B * (((i : ℝ) + 1) ^ rateDegree)) :
    ∃ l r : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (r n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ r n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (r n)))) (fun n => y (k (l (r n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (r n))) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + |g (τ (k (l (r n))))|) ^ 2 /
            ((k (l (r n)) : ℝ) + 1))
        atTop atTop := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMDissipationCorridor
      hH3 hNoExtension hClass hb hg hWitness C growthDegree hGrowthCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | ⟨hPhysical, _⟩
  · exact hVorticity
  have hLarge := physicalRates_superpolynomial_min
    (fun n =>
      velocityH3DissipationAt u (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    (fun n => h3PathTransportExcessRate u (τ (k (l (r n)))))
    (fun n =>
      (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    (fun degree n => (((k (l (r n)) : ℝ) + 1) ^ degree))
    (fun degree n => by positivity)
    (fun degree => (hPhysical degree).1)
    (fun degree => (hPhysical degree).2.1)
    (fun degree => (hPhysical degree).2.2)
    rateDegree B
  have hCeilingSelected := hIndex.eventually hPhysicalCeiling
  obtain ⟨n, hnCeiling, hnLarge⟩ := (hCeilingSelected.and hLarge).exists
  exact False.elim ((not_lt_of_ge hnCeiling) hnLarge)

end

end Euclidean
end Bridge
end PrimeTensor
