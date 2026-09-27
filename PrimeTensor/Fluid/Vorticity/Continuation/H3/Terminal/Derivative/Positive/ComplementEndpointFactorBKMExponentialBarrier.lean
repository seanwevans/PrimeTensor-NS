import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorTransportExcessBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.BKMFrequencyForcing

/-!
# Canonical BKM product on the exponential frequency branch

At positive-growth times, the existing BKM estimate bounds twice the
full dissipation-to-energy ratio above by the vorticity and logarithmic
energy endpoint product. On the persistent frequency branch that
product must therefore exceed every fixed exponential square-root
index scale, up to one fixed kinetic-anchor coefficient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The canonical BKM endpoint product bounds twice the normalized
full dissipation at each selected positive-growth time. -/
theorem positiveGrowth_nativeWitness_dissipation_le_canonicalBKM
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hNative :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y) :
    ∀ n : ℕ,
      2 * (velocityH3DissipationAt u (τ n) /
        velocityH3EnergyAt u (τ n)) <
      4422 *
        (h3BKMCanonicalSelectedLogGradientConstant
          (Real.sqrt (velocityH3Energy0At u b)) + 1) *
        (1 + |g (τ n)|) *
        (1 + Real.log (velocityH3EnergyAt u (τ n))) := by
  obtain ⟨hAt, _, _, _, _, _, _, _, _⟩ := hNative
  intro n
  have hDerivative : 0 < deriv (velocityH3EnergyAt u) (τ n) := by
    have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact lt_of_le_of_lt hnNonneg (hAt n).2.2.1
  exact
    two_mul_dissipation_div_energy_lt_canonicalBKM_vorticityLogFactor_of_pos_deriv
      hH3 hClass hb hg (hAt n).1 hDerivative

/-- Either the normalized vorticity factor diverges or the canonical
BKM endpoint product dominates every exponential square-root-index
scale along the same native relative-escape witness. The latter
conclusion uses a vorticity envelope on the later tail. -/
theorem endpointFactor_relativeRefinedWitness_canonicalBKMExponentialBarrier
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
          2 * Real.exp (M * Real.sqrt ((k (l n) : ℝ) + 1)) ^ 2 <
            (4 + 3 * velocityH3Energy0At u b) *
              (4422 *
                (h3BKMCanonicalSelectedLogGradientConstant
                  (Real.sqrt (velocityH3Energy0At u b)) + 1) *
                (1 + |g (τ (k (l n)))|) *
                (1 + Real.log
                  (velocityH3EnergyAt u (τ (k (l n)))))))) := by
  obtain ⟨l, hNative, hRatio, hBarrier⟩ :=
    endpointFactor_relativeRefinedWitness_dissipationExponentialBarrier
      hH3 hNoExtension hClass hb hWitness
  have hBKM :=
    positiveGrowth_nativeWitness_dissipation_le_canonicalBKM
      hH3 hClass hb hg hNative
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hCPos : 0 < 4 + 3 * velocityH3Energy0At u b := by
    linarith
  refine ⟨l, hNative, hRatio, ?_⟩
  rcases hBarrier with hVorticity | hDissipation
  · exact Or.inl hVorticity
  · refine Or.inr ?_
    intro M hM
    filter_upwards [hDissipation M hM] with n hn
    have hFirst :
        2 * Real.exp (M * Real.sqrt ((k (l n) : ℝ) + 1)) ^ 2 ≤
          (4 + 3 * velocityH3Energy0At u b) *
            (2 * (velocityH3DissipationAt u (τ (k (l n))) /
              velocityH3EnergyAt u (τ (k (l n))))) := by
      calc
        _ ≤ 2 * ((4 + 3 * velocityH3Energy0At u b) *
            (velocityH3DissipationAt u (τ (k (l n))) /
              velocityH3EnergyAt u (τ (k (l n))))) :=
          mul_le_mul_of_nonneg_left hn (by norm_num)
        _ = _ := by ring
    exact lt_of_le_of_lt hFirst
      (mul_lt_mul_of_pos_left (hBKM n) hCPos)

end

end Euclidean
end Bridge
end PrimeTensor
