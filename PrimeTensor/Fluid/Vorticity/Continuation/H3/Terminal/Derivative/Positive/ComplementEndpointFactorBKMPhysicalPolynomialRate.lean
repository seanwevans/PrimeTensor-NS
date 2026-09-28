import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMPhysicalSuperpolynomial

/-!
# Normalized physical rates on the endpoint frequency branch

The every-polynomial lower bound has an equivalent filter-limit form:
after dividing by any fixed power of the original index, the
smaller anchored dissipation and transport rate still tends to
infinity along the common native relative-escape witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Uniform eventual bounds above every nonnegative polynomial
coefficient give divergence after division by each index power. -/
theorem superpolynomial_physicalRate_atTop
    (m : ℕ → ℕ) (R : ℕ → ℝ)
    (hRate : ∀ C : ℝ, 0 ≤ C → ∀ degree : ℕ,
      ∀ᶠ n : ℕ in atTop,
        C * ((m n : ℝ) + 1) ^ degree < R n) :
    ∀ degree : ℕ,
      Tendsto
        (fun n : ℕ => R n / (((m n : ℝ) + 1) ^ degree))
        atTop atTop := by
  intro degree
  refine tendsto_atTop.2 ?_
  intro C
  let D : ℝ := max C 0
  have hDNonneg : 0 ≤ D := le_max_right C 0
  have hCLeD : C ≤ D := le_max_left C 0
  filter_upwards [hRate D hDNonneg degree] with n hn
  have hDen : 0 < ((m n : ℝ) + 1) ^ degree := by
    positivity
  have hDiv : D < R n / (((m n : ℝ) + 1) ^ degree) :=
    (lt_div_iff₀ hDen).2 hn
  exact hCLeD.trans (le_of_lt hDiv)

/-- Either the normalized vorticity factor diverges, or the smaller
anchored physical rate outruns each original-index power as a limit. -/
theorem endpointFactor_relativeRefinedWitness_BKMPhysicalPolynomialRate
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
        u b T p sCurl sGradient τ y k g ratio) :
    ∃ l q : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (q n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ q n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (q n)))) (fun n => y (k (l (q n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (q n))) ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (l (q n))))|) ^ 2 /
              ((k (l (q n)) : ℝ) + 1))
          atTop atTop ∨
        (∀ degree : ℕ,
          Tendsto
            (fun n : ℕ =>
              min
                  ((4 + 3 * velocityH3Energy0At u b) *
                    (velocityH3DissipationAt u (τ (k (l (q n)))) /
                      velocityH3EnergyAt u (τ (k (l (q n))))))
                  ((4 + 3 * velocityH3Energy0At u b) *
                    h3PathTransportExcessRate u (τ (k (l (q n))))) /
                (((k (l (q n)) : ℝ) + 1) ^ degree))
            atTop atTop)) := by
  obtain ⟨l, q, hIndex, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMPhysicalSuperpolynomial
      hH3 hNoExtension hClass hb hg hWitness
  refine ⟨l, q, hIndex, hqIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | hPhysical
  · exact Or.inl hVorticity
  exact Or.inr
    (superpolynomial_physicalRate_atTop
      (fun n => k (l (q n)))
      (fun n =>
        min
          ((4 + 3 * velocityH3Energy0At u b) *
            (velocityH3DissipationAt u (τ (k (l (q n)))) /
              velocityH3EnergyAt u (τ (k (l (q n))))))
          ((4 + 3 * velocityH3Energy0At u b) *
            h3PathTransportExcessRate u (τ (k (l (q n))))))
      hPhysical)

end

end Euclidean
end Bridge
end PrimeTensor
