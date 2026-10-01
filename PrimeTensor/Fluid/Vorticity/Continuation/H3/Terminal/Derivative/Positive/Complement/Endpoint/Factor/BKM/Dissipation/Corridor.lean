import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Growth.Ceiling

/-!
# Dissipation corridor under a polynomial growth ceiling

On the positive-growth witness, normalized dissipation is no larger
than the one-copy excess. In the dissipation-dominant branch the
excess is at most twice normalized dissipation. Exact balance then
puts adverse transport per energy between twice and three times
normalized dissipation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Abstract one-copy excess and adverse-transport corridor. -/
theorem physicalDissipation_corridor
    (Q R A : ℕ → ℝ)
    (hLower : ∀ n, R n ≤ Q n)
    (hBalance : ∀ n, A n = Q n + R n)
    (hUpper : ∀ᶠ n : ℕ in atTop, Q n ≤ 2 * R n) :
    ∀ᶠ n : ℕ in atTop,
      R n ≤ Q n ∧ Q n ≤ 2 * R n ∧
        2 * R n ≤ A n ∧ A n ≤ 3 * R n := by
  filter_upwards [hUpper] with n hn
  have hl := hLower n
  have he := hBalance n
  constructor
  · exact hl
  constructor
  · exact hn
  constructor <;> linarith

/-- Under a polynomial ceiling on normalized H³ energy growth,
either vorticity escapes at its normalized rate or all three
physical rates persist in a sharp dissipation corridor. -/
theorem endpointFactor_relativeRefinedWitness_BKMDissipationCorridor
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
    (C : ℝ) (degree : ℕ)
    (hCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ degree)) :
    ∃ l r : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (r n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ r n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (r n)))) (fun n => y (k (l (r n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (r n))) ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (l (r n))))|) ^ 2 /
              ((k (l (r n)) : ℝ) + 1))
          atTop atTop ∨
        (H3TerminalEndpointPhysicalRateData u τ
            (fun n => k (l (r n))) ∧
          (∀ᶠ n : ℕ in atTop,
            velocityH3DissipationAt u (τ (k (l (r n)))) /
                velocityH3EnergyAt u (τ (k (l (r n)))) ≤
              h3PathTransportExcessRate u (τ (k (l (r n)))) ∧
            h3PathTransportExcessRate u (τ (k (l (r n)))) ≤
              2 * (velocityH3DissipationAt u (τ (k (l (r n)))) /
                velocityH3EnergyAt u (τ (k (l (r n))))) ∧
            2 * (velocityH3DissipationAt u (τ (k (l (r n)))) /
                velocityH3EnergyAt u (τ (k (l (r n))))) ≤
              (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
                velocityH3EnergyAt u (τ (k (l (r n)))) ∧
            (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
                velocityH3EnergyAt u (τ (k (l (r n)))) ≤
              3 * (velocityH3DissipationAt u (τ (k (l (r n)))) /
                velocityH3EnergyAt u (τ (k (l (r n)))))))) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMGrowthCeiling
      hH3 hNoExtension hClass hb hg hWitness C degree hCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | ⟨hPhysical, hDominance⟩
  · exact Or.inl hVorticity
  right
  refine ⟨hPhysical, ?_⟩
  have hDLe := positiveGrowth_nativeWitness_dissipationRatio_le_transportExcess
    hH3 hClass hb hNative
  have hNativeCopy := hNative
  obtain ⟨hAt, _, _, _, _, _, _, _, _⟩ := hNativeCopy
  have hEq : ∀ n : ℕ,
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
  exact physicalDissipation_corridor
    (fun n => h3PathTransportExcessRate u (τ (k (l (r n)))))
    (fun n =>
      velocityH3DissipationAt u (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    (fun n =>
      (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    hDLe hEq hDominance

end

end Euclidean
end Bridge
end PrimeTensor
