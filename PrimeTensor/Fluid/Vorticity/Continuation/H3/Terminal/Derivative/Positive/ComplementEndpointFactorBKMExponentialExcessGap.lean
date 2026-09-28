import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMRawExponentialRates

/-!
# Endpoint exponential bounds for transport excess and the raw balance gap

On the selected physical witness, normalized one-copy transport excess is at
least normalized dissipation. The exact H³ balance identifies the raw gap
between adverse transport and energy growth with twice raw dissipation. The
exponential frequency barrier therefore controls both quantities on that
same witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The physical corridor and exact balance transfer each exponential
polynomial frequency barrier to normalized excess and the raw balance gap. -/
theorem endpointFactor_relativeRefinedWitness_exponentialExcessGap
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
              h3PathTransportExcessRate u (τ (k (l (r n)))) ∧
          2 * Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
            (4 + 3 * velocityH3Energy0At u b) *
              ((-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) -
                deriv (velocityH3EnergyAt u) (τ (k (l (r n)))))) := by
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
  filter_upwards [hRates M degree, hPhysical.2] with n hnRates hnCorridor
  have hExcess :
      Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
        (4 + 3 * velocityH3Energy0At u b) *
          h3PathTransportExcessRate u (τ (k (l (r n)))) :=
    hnRates.2.trans_le
      (mul_le_mul_of_nonneg_left hnCorridor.1 hAnchorPos.le)
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
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  have hGapEq :
      (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) -
          deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) =
        2 * velocityH3DissipationAt u (τ (k (l (r n)))) := by
    linarith
  have hDouble :
      2 * Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
        (4 + 3 * velocityH3Energy0At u b) *
          (2 * velocityH3DissipationAt u (τ (k (l (r n))))) := by
    calc
      _ < 2 * ((4 + 3 * velocityH3Energy0At u b) *
          velocityH3DissipationAt u (τ (k (l (r n))))) :=
        mul_lt_mul_of_pos_left hRawD (by norm_num)
      _ = _ := by ring
  exact ⟨hExcess, by rw [hGapEq]; exact hDouble⟩

end

end Euclidean
end Bridge
end PrimeTensor
