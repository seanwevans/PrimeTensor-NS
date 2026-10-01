import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Relative.Growth.Vanishing

/-!
# Asymptotic physical balance on the selected endpoint witness

The exact positive-growth balance writes the one-copy transport excess as
normalized energy growth plus normalized dissipation. Adverse transport is
then the excess plus a second copy of dissipation. When the growth share
vanishes, their ratios to dissipation tend respectively to one and two.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The two exact sums retain their leading dissipation coefficients
when energy growth is negligible compared with positive dissipation. -/
theorem physicalRates_asymptoticBalance
    (G D Q A : ℕ → ℝ)
    (hDPos : ∀ᶠ n : ℕ in atTop, 0 < D n)
    (hQ : ∀ n, Q n = G n + D n)
    (hA : ∀ n, A n = Q n + D n)
    (hGrowth : Tendsto (fun n => G n / D n) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => Q n / D n) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun n => A n / D n) atTop (𝓝 (2 : ℝ)) := by
  have hQEq :
      (fun n => Q n / D n) =ᶠ[atTop]
        (fun n => G n / D n + 1) := by
    filter_upwards [hDPos] with n hn
    rw [hQ n]
    field_simp [ne_of_gt hn] <;> ring
  have hAEq :
      (fun n => A n / D n) =ᶠ[atTop]
        (fun n => G n / D n + 2) := by
    filter_upwards [hDPos] with n hn
    rw [hA n, hQ n]
    field_simp [ne_of_gt hn] <;> ring
  constructor
  · have hLimit :
        Tendsto (fun n => G n / D n + 1) atTop (𝓝 ((0 : ℝ) + 1)) :=
      hGrowth.add tendsto_const_nhds
    simpa only [zero_add] using hLimit.congr' hQEq.symm
  · have hLimit :
        Tendsto (fun n => G n / D n + 2) atTop (𝓝 ((0 : ℝ) + 2)) :=
      hGrowth.add tendsto_const_nhds
    simpa only [zero_add] using hLimit.congr' hAEq.symm

/-- Under polynomial normalized energy growth and bounded normalized
vorticity, the physical witness has one copy of dissipation in transport
excess and two copies in adverse transport asymptotically. -/
theorem endpointFactor_relativeRefinedWitness_asymptoticBalance
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
          h3PathTransportExcessRate u (τ (k (l (r n)))) /
            (velocityH3DissipationAt u (τ (k (l (r n)))) /
              velocityH3EnergyAt u (τ (k (l (r n))))))
        atTop (𝓝 (1 : ℝ)) ∧
      Tendsto
        (fun n : ℕ =>
          ((-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
            velocityH3EnergyAt u (τ (k (l (r n))))) /
            (velocityH3DissipationAt u (τ (k (l (r n)))) /
              velocityH3EnergyAt u (τ (k (l (r n))))))
        atTop (𝓝 (2 : ℝ)) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, hGrowth⟩ :=
    endpointFactor_relativeRefinedWitness_relativeGrowthVanishing
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, ?_⟩
  have hNativeCopy := hNative
  obtain ⟨hAt, _, _, hDissipationTop, _, _, _, _, _⟩ := hNativeCopy
  have hDPos : ∀ᶠ n : ℕ in atTop,
      0 < velocityH3DissipationAt u (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))) :=
    hDissipationTop.eventually (eventually_gt_atTop (0 : ℝ))
  have hQ : ∀ n : ℕ,
      h3PathTransportExcessRate u (τ (k (l (r n)))) =
        deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
          velocityH3EnergyAt u (τ (k (l (r n)))) +
        velocityH3DissipationAt u (τ (k (l (r n)))) /
          velocityH3EnergyAt u (τ (k (l (r n)))) := by
    intro n
    have ht : τ (k (l (r n))) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hAt n).1.1, (hAt n).1.2⟩
    have hDerivative :
        0 ≤ deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) :=
      (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n).trans
        (le_of_lt (hAt n).2.2.1)
    exact h3PathTransportExcessRate_eq_deriv_div_energy_add_dissipation_div_energy_of_nonnegative_deriv
      hH3 hClass ht hDerivative
  have hA : ∀ n : ℕ,
      (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
          velocityH3EnergyAt u (τ (k (l (r n)))) =
        h3PathTransportExcessRate u (τ (k (l (r n)))) +
        velocityH3DissipationAt u (τ (k (l (r n)))) /
          velocityH3EnergyAt u (τ (k (l (r n)))) := by
    intro n
    have ht : τ (k (l (r n))) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hAt n).1.1, (hAt n).1.2⟩
    have hDerivative :
        0 ≤ deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) :=
      (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n).trans
        (le_of_lt (hAt n).2.2.1)
    exact (h3PathTransportExcessRate_add_dissipation_div_eq_neg_transport_div
      hH3 hClass ht hDerivative).symm
  exact physicalRates_asymptoticBalance
    (fun n =>
      deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    (fun n =>
      velocityH3DissipationAt u (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    (fun n => h3PathTransportExcessRate u (τ (k (l (r n)))))
    (fun n =>
      (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    hDPos hQ hA hGrowth

end

end Euclidean
end Bridge
end PrimeTensor
