import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMExponentialExcessGap

/-!
# Exponential endpoint rate for the raw one-copy transport excess

At positive energy growth times, normalized one-copy transport excess is
the sum of normalized growth and dissipation. Full H³ energy is at least
one, so the raw sum of growth and dissipation bounds this excess above.
The established exponential rate transfers without changing the witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- At a nonnegative energy derivative, the raw sum of growth and
dissipation bounds the normalized one-copy transport excess. -/
theorem transportExcessRate_le_rawGrowthAddDissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDerivative : 0 ≤ deriv (velocityH3EnergyAt u) t) :
    h3PathTransportExcessRate u t ≤
      deriv (velocityH3EnergyAt u) t + velocityH3DissipationAt u t := by
  rw [h3PathTransportExcessRate_eq_deriv_div_energy_add_dissipation_div_energy_of_nonnegative_deriv
    hH3 hClass ht hDerivative]
  have hEnergyOne : 1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t
  have hDNonneg : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hGrowthLe :=
    dissipation_div_energy_le_raw_of_energy_one
      (deriv (velocityH3EnergyAt u) t) (velocityH3EnergyAt u t)
      hDerivative hEnergyOne
  have hDLe :=
    dissipation_div_energy_le_raw_of_energy_one
      (velocityH3DissipationAt u t) (velocityH3EnergyAt u t)
      hDNonneg hEnergyOne
  linarith

/-- Every fixed exponential polynomial square lies below anchored raw
one-copy excess, together with the previously established raw balance gap,
on the same endpoint physical witness. -/
theorem endpointFactor_relativeRefinedWitness_rawExcessExponential
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
              (deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) +
                velocityH3DissipationAt u (τ (k (l (r n))))) ∧
          2 * Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
            (4 + 3 * velocityH3Energy0At u b) *
              ((-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) -
                deriv (velocityH3EnergyAt u) (τ (k (l (r n)))))) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, hRates⟩ :=
    endpointFactor_relativeRefinedWitness_exponentialExcessGap
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
  have ht : τ (k (l (r n))) ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hAt n).1.1, (hAt n).1.2⟩
  have hDerivative :
      0 ≤ deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) :=
    (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n).trans
      (le_of_lt (hAt n).2.2.1)
  have hExcessLe :=
    transportExcessRate_le_rawGrowthAddDissipation
      hH3 hClass ht hDerivative
  exact ⟨hnRates.1.trans_le
      (mul_le_mul_of_nonneg_left hExcessLe hAnchorPos.le), hnRates.2⟩

end

end Euclidean
end Bridge
end PrimeTensor
