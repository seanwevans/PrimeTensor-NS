import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMAdverseTransportRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.NormalizedBalanceGap

/-!
# Exact balance-gap rate on the endpoint frequency branch

The normalized difference between adverse transport and the H³
energy derivative equals twice normalized full dissipation. Hence
the endpoint frequency branch forces this exact balance gap above
every original-index polynomial on the same native witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A superpolynomial normalized dissipation rate transfers to the
exact adverse-transport minus energy-growth balance gap. -/
theorem positiveGrowth_nativeWitness_balanceGap_polynomialRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {τ : ℕ → ℝ}
    {m : ℕ → ℕ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ (m n) ∈ Set.Ioo a T)
    (hDissipation : ∀ degree : ℕ,
      Tendsto
        (fun n : ℕ =>
          (velocityH3DissipationAt u (τ (m n)) /
            velocityH3EnergyAt u (τ (m n))) /
            (((m n : ℝ) + 1) ^ degree))
        atTop atTop) :
    ∀ degree : ℕ,
      Tendsto
        (fun n : ℕ =>
          (((-velocityH3TransportDerivativeAt u (τ (m n))) -
            deriv (velocityH3EnergyAt u) (τ (m n))) /
            velocityH3EnergyAt u (τ (m n))) /
            (((m n : ℝ) + 1) ^ degree))
        atTop atTop := by
  intro degree
  have hTwice : Tendsto
      (fun n : ℕ =>
        2 * ((velocityH3DissipationAt u (τ (m n)) /
          velocityH3EnergyAt u (τ (m n))) /
          (((m n : ℝ) + 1) ^ degree)))
      atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      (hDissipation degree)
  have hEq :
      (fun n : ℕ =>
        (((-velocityH3TransportDerivativeAt u (τ (m n))) -
          deriv (velocityH3EnergyAt u) (τ (m n))) /
          velocityH3EnergyAt u (τ (m n))) /
          (((m n : ℝ) + 1) ^ degree)) =
        (fun n : ℕ =>
          2 * ((velocityH3DissipationAt u (τ (m n)) /
            velocityH3EnergyAt u (τ (m n))) /
            (((m n : ℝ) + 1) ^ degree))) := by
    funext n
    rw [normalized_negativeTransport_sub_deriv_eq_two_mul_dissipation_div_energy
      hH3 hClass (hAt n)]
    ring
  rw [hEq]
  exact hTwice

/-- Either the normalized vorticity factor escapes, or the exact
normalized balance gap outruns each original-index power. -/
theorem endpointFactor_relativeRefinedWitness_BKMBalanceGapRate
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
              (((-velocityH3TransportDerivativeAt u (τ (k (l (q n))))) -
                deriv (velocityH3EnergyAt u) (τ (k (l (q n))))) /
                velocityH3EnergyAt u (τ (k (l (q n))))) /
                (((k (l (q n)) : ℝ) + 1) ^ degree))
            atTop atTop)) := by
  obtain ⟨l, q, hIndex, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMAdverseTransportRate
      hH3 hNoExtension hClass hb hg hWitness
  refine ⟨l, q, hIndex, hqIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | hPhysical
  · exact Or.inl hVorticity
  right
  obtain ⟨hAt, _, _, _, _, _, _, _, _⟩ := hNative
  exact positiveGrowth_nativeWitness_balanceGap_polynomialRate
    (τ := τ) (m := fun n => k (l (q n)))
    hH3 hClass
    (fun n => ⟨lt_trans hb.1 (hAt n).1.1, (hAt n).1.2⟩)
    (fun degree => (hPhysical degree).1)

end

end Euclidean
end Bridge
end PrimeTensor
