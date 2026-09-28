import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMAdverseTransportRate

/-!
# Raw physical rates on the endpoint frequency branch

The H³ energy is at least one. Thus superpolynomial growth after
normalization by energy already forces superpolynomial growth of
the full dissipation and adverse transport numerator themselves.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A rate escaping after division by both an energy of at least one
and a positive scale also escapes after division by the scale alone. -/
theorem physicalRate_unscaled_atTop
    (R E P : ℕ → ℝ)
    (hE : ∀ n, 1 ≤ E n)
    (hP : ∀ n, 0 < P n)
    (hRate : Tendsto
      (fun n => (R n / E n) / P n) atTop atTop) :
    Tendsto (fun n => R n / P n) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro C
  let D : ℝ := max C 0
  have hDNonneg : 0 ≤ D := le_max_right C 0
  have hCLeD : C ≤ D := le_max_left C 0
  filter_upwards [hRate.eventually (eventually_ge_atTop D)] with n hn
  have hFirst : D * P n ≤ R n / E n :=
    (le_div_iff₀ (hP n)).1 hn
  have hEPos : 0 < E n := by linarith [hE n]
  have hSecond : (D * P n) * E n ≤ R n :=
    (le_div_iff₀ hEPos).1 hFirst
  have hProductNonneg : 0 ≤ D * P n :=
    mul_nonneg hDNonneg (le_of_lt (hP n))
  have hLower : D * P n ≤ (D * P n) * E n := by
    have hExtra : 0 ≤ (D * P n) * (E n - 1) :=
      mul_nonneg hProductNonneg (by linarith [hE n])
    nlinarith
  have hCProduct : C * P n ≤ D * P n :=
    mul_le_mul_of_nonneg_right hCLeD (le_of_lt (hP n))
  exact (le_div_iff₀ (hP n)).2
    (hCProduct.trans (hLower.trans hSecond))

/-- Either the normalized vorticity factor escapes, or full H³
dissipation and adverse transport themselves outrun every fixed
power of the original index on one native relative-escape witness. -/
theorem endpointFactor_relativeRefinedWitness_BKMRawPhysicalRates
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
              velocityH3DissipationAt u (τ (k (l (q n)))) /
                (((k (l (q n)) : ℝ) + 1) ^ degree))
            atTop atTop ∧
          Tendsto
            (fun n : ℕ =>
              (-velocityH3TransportDerivativeAt u (τ (k (l (q n))))) /
                (((k (l (q n)) : ℝ) + 1) ^ degree))
            atTop atTop)) := by
  obtain ⟨l, q, hIndex, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMAdverseTransportRate
      hH3 hNoExtension hClass hb hg hWitness
  refine ⟨l, q, hIndex, hqIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | hPhysical
  · exact Or.inl hVorticity
  right
  intro degree
  obtain ⟨hDissipation, _, hTransport⟩ := hPhysical degree
  have hEnergy : ∀ n : ℕ,
      1 ≤ velocityH3EnergyAt u (τ (k (l (q n)))) :=
    fun n => one_le_velocityH3EnergyAt _ _
  have hScale : ∀ n : ℕ,
      0 < (((k (l (q n)) : ℝ) + 1) ^ degree) :=
    fun n => by positivity
  exact ⟨
    physicalRate_unscaled_atTop
      (fun n => velocityH3DissipationAt u (τ (k (l (q n)))))
      (fun n => velocityH3EnergyAt u (τ (k (l (q n)))))
      (fun n => ((k (l (q n)) : ℝ) + 1) ^ degree)
      hEnergy hScale hDissipation,
    physicalRate_unscaled_atTop
      (fun n => -velocityH3TransportDerivativeAt u (τ (k (l (q n)))))
      (fun n => velocityH3EnergyAt u (τ (k (l (q n)))))
      (fun n => ((k (l (q n)) : ℝ) + 1) ^ degree)
      hEnergy hScale hTransport⟩

end

end Euclidean
end Bridge
end PrimeTensor
