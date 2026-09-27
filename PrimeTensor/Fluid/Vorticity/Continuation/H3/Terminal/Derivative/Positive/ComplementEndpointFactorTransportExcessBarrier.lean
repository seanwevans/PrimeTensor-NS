import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorFrequencyDissipationBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.TransportExcessRateCascade

/-!
# Adverse transport excess on the exponential frequency branch

At every selected positive-growth time, the normalized transport
excess dominates full dissipation divided by energy. Thus the
exponential lower bound on normalized dissipation transfers to the
transport excess on the same relative-escape witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Positive growth makes normalized full dissipation no larger than
the transport excess at every time of a quantitative native witness. -/
theorem positiveGrowth_nativeWitness_dissipationRatio_le_transportExcess
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hNative :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y) :
    ∀ n : ℕ,
      velocityH3DissipationAt u (τ n) /
          velocityH3EnergyAt u (τ n) ≤
        h3PathTransportExcessRate u (τ n) := by
  obtain ⟨hAt, _, _, _, _, _, _, _, _⟩ := hNative
  intro n
  have hClassTime : τ n ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hAt n).1.1, (hAt n).1.2⟩
  have hDerivative : 0 ≤ deriv (velocityH3EnergyAt u) (τ n) := by
    have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact hnNonneg.trans (le_of_lt (hAt n).2.2.1)
  exact velocityH3Dissipation_div_energy_le_transportExcessRate_of_nonnegative_deriv
    hH3 hClass hClassTime hDerivative

/-- Relative escape forces either the vorticity factor's normalized
rate or an exponential square-root-index lower bound on adverse
H³ transport excess, with one common native and ratio witness. -/
theorem endpointFactor_relativeRefinedWitness_transportExcessExponentialBarrier
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
    (hWitness :
      H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio) :
    ∃ l : ℕ → ℕ,
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l n))) (fun n => y (k (l n))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l n)) ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (l n)))|) ^ 2 /
              ((k (l n) : ℝ) + 1))
          atTop atTop ∨
        (∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
          Real.exp (M * Real.sqrt ((k (l n) : ℝ) + 1)) ^ 2 ≤
            (4 + 3 * velocityH3Energy0At u b) *
              h3PathTransportExcessRate u (τ (k (l n))))) := by
  obtain ⟨l, hNative, hRatio, hBarrier⟩ :=
    endpointFactor_relativeRefinedWitness_dissipationExponentialBarrier
      hH3 hNoExtension hClass hb hWitness
  have hDLe :=
    positiveGrowth_nativeWitness_dissipationRatio_le_transportExcess
      hH3 hClass hb hNative
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hCNonneg : 0 ≤ 4 + 3 * velocityH3Energy0At u b := by
    linarith
  refine ⟨l, hNative, hRatio, ?_⟩
  rcases hBarrier with hVorticity | hDissipation
  · exact Or.inl hVorticity
  · refine Or.inr ?_
    intro M hM
    filter_upwards [hDissipation M hM] with n hn
    exact hn.trans
      (mul_le_mul_of_nonneg_left (hDLe n) hCNonneg)

end

end Euclidean
end Bridge
end PrimeTensor
