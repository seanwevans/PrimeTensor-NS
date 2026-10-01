import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Exponential.Dissipation.Rate

/-!
# Raw dissipation and adverse transport at the exponential endpoint rate

The full H³ energy is at least one, so an anchored lower bound for
normalized dissipation transfers to raw dissipation. Positive energy
growth and the exact H³ balance put raw adverse transport above raw
dissipation at every selected time. The exponential polynomial barrier
therefore persists for both raw physical quantities on one witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- If energy is at least one and dissipation is nonnegative, the raw
dissipation bounds its energy-normalized value above. -/
theorem dissipation_div_energy_le_raw_of_energy_one
    (D E : ℝ) (hD : 0 ≤ D) (hE : 1 ≤ E) :
    D / E ≤ D := by
  have hEPos : 0 < E := by linarith
  apply (div_le_iff₀ hEPos).2
  have hMul := mul_le_mul_of_nonneg_left hE hD
  nlinarith

/-- With the growth and vorticity ceilings selecting the physical
branch, every fixed exponential polynomial square is eventually below
an anchored raw dissipation and raw adverse-transport rate. -/
theorem endpointFactor_relativeRefinedWitness_rawExponentialRates
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
      (∀ M : ℝ, ∀ degree : ℕ,
        ∀ᶠ n : ℕ in atTop,
          Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
            (4 + 3 * velocityH3Energy0At u b) *
              velocityH3DissipationAt u (τ (k (l (r n)))) ∧
          Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
            (4 + 3 * velocityH3Energy0At u b) *
              (-velocityH3TransportDerivativeAt u (τ (k (l (r n)))))) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio,
      hPhysical, _, _, _, hRates⟩ :=
    endpointFactor_relativeRefinedWitness_exponentialDissipationRate
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, ?_⟩
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hAnchorPos : 0 < 4 + 3 * velocityH3Energy0At u b := by
    linarith
  have hNativeCopy := hNative
  obtain ⟨hAt, _, _, _, _, _, _, _, _⟩ := hNativeCopy
  intro M degree
  filter_upwards [hRates M degree] with n hnRates
  have hEnergyOne : 1 ≤ velocityH3EnergyAt u (τ (k (l (r n)))) :=
    one_le_velocityH3EnergyAt _ _
  have hDNonneg : 0 ≤ velocityH3DissipationAt u (τ (k (l (r n)))) :=
    velocityH3DissipationAt_nonneg _ _
  have hDNormalizedLe :
      velocityH3DissipationAt u (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))) ≤
      velocityH3DissipationAt u (τ (k (l (r n)))) :=
    dissipation_div_energy_le_raw_of_energy_one _ _ hDNonneg hEnergyOne
  have hRawD :
      Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
        (4 + 3 * velocityH3Energy0At u b) *
          velocityH3DissipationAt u (τ (k (l (r n)))) :=
    hnRates.2.trans_le
      (mul_le_mul_of_nonneg_left hDNormalizedLe hAnchorPos.le)
  have ht : τ (k (l (r n))) ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hAt n).1.1, (hAt n).1.2⟩
  have hDerivative :
      0 ≤ deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) :=
    (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n).trans
      (le_of_lt (hAt n).2.2.1)
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  have hDLeTransport :
      velocityH3DissipationAt u (τ (k (l (r n)))) ≤
        -velocityH3TransportDerivativeAt u (τ (k (l (r n)))) := by
    linarith
  exact ⟨hRawD,
    hRawD.trans_le
      (mul_le_mul_of_nonneg_left hDLeTransport hAnchorPos.le)⟩

end

end Euclidean
end Bridge
end PrimeTensor
