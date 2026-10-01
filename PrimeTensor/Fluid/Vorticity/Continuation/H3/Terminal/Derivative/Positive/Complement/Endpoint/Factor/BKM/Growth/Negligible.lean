import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Joint.Polynomial.Ceiling

/-!
# Normalized energy growth beneath superpolynomial dissipation

On the physical branch selected by a bounded normalized vorticity
factor, a polynomial ceiling on energy growth is eventually smaller
than every positive multiple of normalized dissipation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A polynomially bounded rate lies below every positive multiple
of a rate that escapes relative to the same scale. -/
theorem polynomialRate_eventually_le_fraction_of_superpolynomialRate
    (G D scale : ℕ → ℝ)
    (hScale : ∀ n, 0 < scale n)
    (C : ℝ)
    (hG : ∀ᶠ n : ℕ in atTop, G n ≤ C * scale n)
    (hD : Tendsto (fun n : ℕ => D n / scale n) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, G n ≤ ε * D n := by
  have hLarge := hD.eventually (eventually_gt_atTop (C / ε))
  filter_upwards [hG, hLarge] with n hnG hnD
  have hDLower : (C / ε) * scale n < D n :=
    (lt_div_iff₀ (hScale n)).mp hnD
  have hEq : ε * ((C / ε) * scale n) = C * scale n := by
    field_simp [ne_of_gt hε] <;> ring
  calc
    G n ≤ C * scale n := hnG
    _ = ε * ((C / ε) * scale n) := hEq.symm
    _ ≤ ε * D n :=
      mul_le_mul_of_nonneg_left (le_of_lt hDLower) hε.le

/-- In the selected physical branch, normalized energy growth is
asymptotically dominated by normalized dissipation in the one-sided
sense of every positive multiplicative bound. -/
theorem endpointFactor_relativeRefinedWitness_growthNegligibleOfVorticityCeiling
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
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B) :
    ∃ l r : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (r n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ r n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (r n)))) (fun n => y (k (l (r n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (r n))) ∧
      H3TerminalEndpointPhysicalDissipationCorridorData u τ
        (fun n => k (l (r n))) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
              velocityH3EnergyAt u (τ (k (l (r n)))) ≤
            ε * (velocityH3DissipationAt u (τ (k (l (r n)))) /
              velocityH3EnergyAt u (τ (k (l (r n))))) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical⟩ :=
    endpointFactor_relativeRefinedWitness_physical_of_vorticityCeiling
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, ?_⟩
  have hRates : H3TerminalEndpointPhysicalRateData u τ
      (fun n => k (l (r n))) := hPhysical.1
  intro ε hε
  exact polynomialRate_eventually_le_fraction_of_superpolynomialRate
    (fun n =>
      deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    (fun n =>
      velocityH3DissipationAt u (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    (fun n => (((k (l (r n)) : ℝ) + 1) ^ growthDegree))
    (fun n => by positivity)
    C (hIndex.eventually hGrowthCeiling)
    ((hRates growthDegree).1)
    ε hε

end

end Euclidean
end Bridge
end PrimeTensor
