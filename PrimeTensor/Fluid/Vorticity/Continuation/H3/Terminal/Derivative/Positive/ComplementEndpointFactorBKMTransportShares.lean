import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMAsymptoticBalance

/-!
# Shares of adverse transport on the endpoint physical witness

The selected physical branch has normalized transport excess asymptotic to
one copy of dissipation and adverse transport asymptotic to two copies.
Exact balance then makes the energy-growth share of adverse transport vanish,
while transport excess accounts for one half of adverse transport.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A ratio of two rates may be formed from their ratios to the same
eventually positive reference rate. -/
theorem ratio_tendsto_of_common_positive_reference
    (X Y D : ℕ → ℝ) (x y : ℝ)
    (hDPos : ∀ᶠ n : ℕ in atTop, 0 < D n)
    (hYPos : ∀ᶠ n : ℕ in atTop, 0 < Y n)
    (hX : Tendsto (fun n => X n / D n) atTop (𝓝 x))
    (hY : Tendsto (fun n => Y n / D n) atTop (𝓝 y))
    (hy : y ≠ 0) :
    Tendsto (fun n => X n / Y n) atTop (𝓝 (x / y)) := by
  have hRatio := hX.div hY hy
  have hEq :
      (fun n => (X n / D n) / (Y n / D n)) =ᶠ[atTop]
        (fun n => X n / Y n) := by
    filter_upwards [hDPos, hYPos] with n hnD hnY
    field_simp [ne_of_gt hnD, ne_of_gt hnY]
  exact hRatio.congr' hEq

/-- With polynomial normalized energy growth and bounded normalized
vorticity, growth occupies a vanishing fraction of adverse transport;
the one-copy excess occupies asymptotically one half. -/
theorem endpointFactor_relativeRefinedWitness_transportShares
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
          ((-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
            velocityH3EnergyAt u (τ (k (l (r n))))))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto
        (fun n : ℕ =>
          h3PathTransportExcessRate u (τ (k (l (r n)))) /
          ((-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
            velocityH3EnergyAt u (τ (k (l (r n))))))
        atTop (𝓝 ((1 : ℝ) / 2)) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, hQDiv, hADiv⟩ :=
    endpointFactor_relativeRefinedWitness_asymptoticBalance
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, ?_⟩
  have hNativeCopy := hNative
  obtain ⟨hAt, _, _, hDissipationTop, _, _, _, _, _⟩ := hNativeCopy
  have hDPos : ∀ᶠ n : ℕ in atTop,
      0 < velocityH3DissipationAt u (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))) :=
    hDissipationTop.eventually (eventually_gt_atTop (0 : ℝ))
  have hAPos : ∀ᶠ n : ℕ in atTop,
      0 < (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
        velocityH3EnergyAt u (τ (k (l (r n)))) := by
    filter_upwards [hDPos, hPhysical.2] with n hnD hnCorridor
    exact (mul_pos (by norm_num : (0 : ℝ) < 2) hnD).trans_le
      hnCorridor.2.2.1
  have hGDiv : Tendsto
      (fun n : ℕ =>
        (deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
          velocityH3EnergyAt u (τ (k (l (r n))))) /
        (velocityH3DissipationAt u (τ (k (l (r n)))) /
          velocityH3EnergyAt u (τ (k (l (r n))))))
      atTop (𝓝 (0 : ℝ)) := by
    have hEq :
        (fun n : ℕ =>
          h3PathTransportExcessRate u (τ (k (l (r n)))) /
            (velocityH3DissipationAt u (τ (k (l (r n)))) /
              velocityH3EnergyAt u (τ (k (l (r n))))) - 1) =ᶠ[atTop]
        (fun n : ℕ =>
          (deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
            velocityH3EnergyAt u (τ (k (l (r n))))) /
          (velocityH3DissipationAt u (τ (k (l (r n)))) /
            velocityH3EnergyAt u (τ (k (l (r n)))))) := by
      filter_upwards [hDPos] with n hnD
      have ht : τ (k (l (r n))) ∈ Set.Ioo a T :=
        ⟨lt_trans hb.1 (hAt n).1.1, (hAt n).1.2⟩
      have hDerivative :
          0 ≤ deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) :=
        (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n).trans
          (le_of_lt (hAt n).2.2.1)
      rw [h3PathTransportExcessRate_eq_deriv_div_energy_add_dissipation_div_energy_of_nonnegative_deriv
        hH3 hClass ht hDerivative, add_div, div_self (ne_of_gt hnD)]
      ring
    simpa only [sub_self] using (hQDiv.sub_const 1).congr' hEq
  constructor
  · simpa only [zero_div] using
      ratio_tendsto_of_common_positive_reference
        (fun n =>
          deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
            velocityH3EnergyAt u (τ (k (l (r n)))))
        (fun n =>
          (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
            velocityH3EnergyAt u (τ (k (l (r n)))))
        (fun n =>
          velocityH3DissipationAt u (τ (k (l (r n)))) /
            velocityH3EnergyAt u (τ (k (l (r n)))))
        0 2 hDPos hAPos hGDiv hADiv (by norm_num)
  · exact ratio_tendsto_of_common_positive_reference
      (fun n => h3PathTransportExcessRate u (τ (k (l (r n)))))
      (fun n =>
        (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
          velocityH3EnergyAt u (τ (k (l (r n)))))
      (fun n =>
        velocityH3DissipationAt u (τ (k (l (r n)))) /
          velocityH3EnergyAt u (τ (k (l (r n)))))
      1 2 hDPos hAPos hQDiv hADiv (by norm_num)

end

end Euclidean
end Bridge
end PrimeTensor
