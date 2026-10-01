import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Physical.Polynomial.Rate

/-!
# Separate normalized physical rates on the endpoint frequency branch

The positive anchor coefficient and the minimum-rate limit yield
superpolynomial normalized growth of full dissipation divided by H³
energy and of adverse transport excess, individually, on the same
refined native witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- If the minimum of two positive-coefficient rates dominates every
multiple of a positive scale, each rate does so individually. -/
theorem physicalMinRate_separate_atTop
    (K : ℝ) (D Q P : ℕ → ℝ)
    (hK : 0 < K) (hP : ∀ n, 0 < P n)
    (hMin : Tendsto
      (fun n => min (K * D n) (K * Q n) / P n) atTop atTop) :
    Tendsto (fun n => D n / P n) atTop atTop ∧
      Tendsto (fun n => Q n / P n) atTop atTop := by
  have hSide (R : ℕ → ℝ)
      (hBound : ∀ n, min (K * D n) (K * Q n) ≤ K * R n) :
      Tendsto (fun n => R n / P n) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro C
    let C₀ : ℝ := max C 0
    have hCLe : C ≤ C₀ := le_max_left C 0
    have hLate : ∀ᶠ n : ℕ in atTop,
        K * C₀ ≤ min (K * D n) (K * Q n) / P n :=
      hMin.eventually (eventually_ge_atTop (K * C₀))
    filter_upwards [hLate] with n hn
    have hMul : (K * C₀) * P n ≤
        min (K * D n) (K * Q n) :=
      (le_div_iff₀ (hP n)).1 hn
    have hKMul : K * (C₀ * P n) ≤ K * R n := by
      calc
        _ = (K * C₀) * P n := by ring
        _ ≤ min (K * D n) (K * Q n) := hMul
        _ ≤ K * R n := hBound n
    have hBoundR : C₀ * P n ≤ R n := by
      by_contra hNot
      have hLt : R n < C₀ * P n := lt_of_not_ge hNot
      exact (not_lt_of_ge hKMul)
        (mul_lt_mul_of_pos_left hLt hK)
    exact hCLe.trans ((le_div_iff₀ (hP n)).2 hBoundR)
  exact ⟨hSide D (fun n => min_le_left _ _),
    hSide Q (fun n => min_le_right _ _)⟩

/-- Either the normalized vorticity factor escapes, or each physical
rate separately grows faster than every original-index power. -/
theorem endpointFactor_relativeRefinedWitness_BKMPhysicalSeparateRates
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
              (velocityH3DissipationAt u (τ (k (l (q n)))) /
                velocityH3EnergyAt u (τ (k (l (q n))))) /
                (((k (l (q n)) : ℝ) + 1) ^ degree))
            atTop atTop ∧
          Tendsto
            (fun n : ℕ =>
              h3PathTransportExcessRate u (τ (k (l (q n)))) /
                (((k (l (q n)) : ℝ) + 1) ^ degree))
            atTop atTop)) := by
  obtain ⟨l, q, hIndex, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMPhysicalPolynomialRate
      hH3 hNoExtension hClass hb hg hWitness
  refine ⟨l, q, hIndex, hqIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | hPhysical
  · exact Or.inl hVorticity
  right
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hK : 0 < 4 + 3 * velocityH3Energy0At u b := by
    linarith
  intro degree
  exact physicalMinRate_separate_atTop
    (4 + 3 * velocityH3Energy0At u b)
    (fun n =>
      velocityH3DissipationAt u (τ (k (l (q n)))) /
        velocityH3EnergyAt u (τ (k (l (q n)))))
    (fun n => h3PathTransportExcessRate u (τ (k (l (q n)))))
    (fun n => ((k (l (q n)) : ℝ) + 1) ^ degree)
    hK (fun n => by positivity) (hPhysical degree)

end

end Euclidean
end Bridge
end PrimeTensor
