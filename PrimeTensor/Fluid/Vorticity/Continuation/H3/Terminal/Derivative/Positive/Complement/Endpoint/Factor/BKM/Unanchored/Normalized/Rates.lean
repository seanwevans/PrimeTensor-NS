import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Exponential.Physical.Ceiling

/-!
# Unanchored exponential rates for normalized dissipation and excess

The frequency square controls anchored normalized full H³ dissipation.
On the selected physical corridor, one-copy transport excess is at least
that normalized dissipation. Since the bounds hold at every coefficient,
the fixed anchor can be removed for both rates on the same witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Every exponential polynomial square is eventually below both
normalized dissipation and one-copy transport excess on one witness. -/
theorem endpointFactor_relativeRefinedWitness_unanchoredNormalizedRates
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
      (∀ A : ℝ, ∀ degree : ℕ,
        ∀ᶠ n : ℕ in atTop,
          Real.exp (A * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
            velocityH3DissipationAt u (τ (k (l (r n)))) /
              velocityH3EnergyAt u (τ (k (l (r n)))) ∧
          Real.exp (A * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
            h3PathTransportExcessRate u (τ (k (l (r n))))) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio,
      hPhysical, _, _, _, hRates⟩ :=
    endpointFactor_relativeRefinedWitness_exponentialDissipationRate
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, ?_⟩
  let anchor : ℝ := 4 + 3 * velocityH3Energy0At u b
  have hAnchorPos : 0 < anchor := by
    dsimp [anchor]
    have hE0 := velocityH3Energy0At_nonneg u b
    linarith
  have hD : ∀ A : ℝ, ∀ degree : ℕ,
      ∀ᶠ n : ℕ in atTop,
        Real.exp (A * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
          anchor * (velocityH3DissipationAt u (τ (k (l (r n)))) /
            velocityH3EnergyAt u (τ (k (l (r n))))) := by
    intro A degree
    exact (hRates A degree).mono (fun n hn => hn.2)
  have hQ : ∀ A : ℝ, ∀ degree : ℕ,
      ∀ᶠ n : ℕ in atTop,
        Real.exp (A * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
          anchor * h3PathTransportExcessRate u (τ (k (l (r n)))) := by
    intro A degree
    filter_upwards [hD A degree, hPhysical.2] with n hnD hnCorridor
    exact hnD.trans_le
      (mul_le_mul_of_nonneg_left hnCorridor.1 hAnchorPos.le)
  have hDUnanchored :=
    unanchored_exponential_square_rate
      (fun n => k (l (r n)))
      (fun n => velocityH3DissipationAt u (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
      anchor hAnchorPos hD
  have hQUnanchored :=
    unanchored_exponential_square_rate
      (fun n => k (l (r n)))
      (fun n => h3PathTransportExcessRate u (τ (k (l (r n)))))
      anchor hAnchorPos hQ
  intro A degree
  filter_upwards [hDUnanchored A degree, hQUnanchored A degree]
    with n hnD hnQ
  exact ⟨hnD, hnQ⟩

end

end Euclidean
end Bridge
end PrimeTensor
