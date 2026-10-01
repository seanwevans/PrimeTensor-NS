import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Growth.Negligible

/-!
# Vanishing energy-growth share of physical dissipation

The selected physical branch has positive normalized dissipation and
nonnegative normalized energy growth. Bounds by every positive
multiple of dissipation therefore give an actual zero limit for their
ratio on the same witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- For eventually positive denominators and nonnegative numerators,
every positive multiplicative bound implies convergence of the ratio
to zero. -/
theorem ratio_tendsto_zero_of_every_positive_fraction
    (G D : ℕ → ℝ)
    (hDPos : ∀ᶠ n : ℕ in atTop, 0 < D n)
    (hGNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ G n)
    (hSmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, G n ≤ ε * D n) :
    Tendsto (fun n : ℕ => G n / D n) atTop (𝓝 (0 : ℝ)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hDPos, hGNonneg] with n hnD hnG
    exact ha.trans_le (div_nonneg hnG hnD.le)
  · intro b hb
    have hHalf : 0 < b / 2 := by linarith
    filter_upwards [hDPos, hSmall (b / 2) hHalf] with n hnD hnSmall
    have hDiv : G n / D n ≤ b / 2 :=
      (div_le_iff₀ hnD).2 hnSmall
    exact lt_of_le_of_lt hDiv (by linarith)

/-- With polynomial energy-growth and bounded normalized vorticity,
the selected physical witness has energy-growth divided by full
normalized dissipation tending to zero. -/
theorem endpointFactor_relativeRefinedWitness_relativeGrowthVanishing
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
      Tendsto
        (fun n : ℕ =>
          (deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
            velocityH3EnergyAt u (τ (k (l (r n))))) /
          (velocityH3DissipationAt u (τ (k (l (r n)))) /
            velocityH3EnergyAt u (τ (k (l (r n))))))
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, hSmall⟩ :=
    endpointFactor_relativeRefinedWitness_growthNegligibleOfVorticityCeiling
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, ?_⟩
  have hNativeCopy := hNative
  obtain ⟨hAt, _, hEnergyTop, hDissipationTop, _, _, _, _, _⟩ := hNativeCopy
  have hEPos := hEnergyTop.eventually (eventually_gt_atTop (0 : ℝ))
  have hDPos := hDissipationTop.eventually (eventually_gt_atTop (0 : ℝ))
  have hGNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))) := by
    filter_upwards [hEPos] with n hnE
    have hnDeriv : 0 ≤ deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) :=
      (Nat.cast_nonneg n).trans (le_of_lt (hAt n).2.2.1)
    exact div_nonneg hnDeriv hnE.le
  exact ratio_tendsto_zero_of_every_positive_fraction
    (fun n =>
      deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    (fun n =>
      velocityH3DissipationAt u (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    hDPos hGNonneg hSmall

end

end Euclidean
end Bridge
end PrimeTensor
