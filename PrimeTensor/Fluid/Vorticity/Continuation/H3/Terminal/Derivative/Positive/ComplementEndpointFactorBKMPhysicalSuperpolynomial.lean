import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMPolynomialCeiling

/-!
# Superpolynomial physical rates on the frequency branch

The endpoint frequency alternative forces both anchored normalized
dissipation and transport excess above every fixed polynomial of the
original index. The two inequalities hold on one common refined
native relative-escape witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A fixed polynomial is strictly below a suitable endpoint
double-exponential scale for every real argument at least one. -/
theorem polynomial_lt_endpointScale
    (C B x : ℝ) (degree : ℕ)
    (hC : 0 ≤ C) (hB : 0 < B) (hx : 1 ≤ x) :
    C * x ^ degree <
      Real.exp
        (Real.exp
          ((B * ((C + 2 * (degree : ℝ)) + 2)) * Real.sqrt x) /
            B - 1) ^ 2 := by
  have hA : 0 ≤ C + 2 * (degree : ℝ) := by
    have hDegree : 0 ≤ (degree : ℝ) := Nat.cast_nonneg degree
    linarith
  have hs : 1 ≤ Real.sqrt x := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  exact (polynomial_le_sqrtExponential C x degree hC hx).trans_lt
    (singleExponential_lt_endpointScale
      (C + 2 * (degree : ℝ)) B (Real.sqrt x) hA hB hs)

/-- The refined witness retains its original index and native data.
Either its vorticity factor escapes at normalized rate, or both
anchored physical rates exceed every fixed original-index polynomial. -/
theorem endpointFactor_relativeRefinedWitness_BKMPhysicalSuperpolynomial
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
        (∀ C : ℝ, 0 ≤ C → ∀ degree : ℕ,
          ∀ᶠ n : ℕ in atTop,
            C * ((k (l (q n)) : ℝ) + 1) ^ degree <
              min
                ((4 + 3 * velocityH3Energy0At u b) *
                  (velocityH3DissipationAt u (τ (k (l (q n)))) /
                    velocityH3EnergyAt u (τ (k (l (q n))))))
                ((4 + 3 * velocityH3Energy0At u b) *
                  h3PathTransportExcessRate u (τ (k (l (q n))))))) := by
  obtain ⟨l, q, hIndex, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMOriginalIndex
      hH3 hNoExtension hClass hb hg hWitness
  refine ⟨l, q, hIndex, hqIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | hPhysical
  · exact Or.inl hVorticity
  right
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hCNonneg : 0 ≤ 4 + 3 * velocityH3Energy0At u b := by
    linarith
  have hBNonneg :
      0 ≤ h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u b)) :=
    h3BKMCanonicalSelectedLogGradientConstant_nonneg
      (Real.sqrt_nonneg _)
  have hCoeffNonneg :
      0 ≤ h3TerminalBKMIntrinsicFrequencyCoefficient u b := by
    unfold h3TerminalBKMIntrinsicFrequencyCoefficient
    exact mul_nonneg hCNonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (by linarith))
        (sq_nonneg _))
  let B := h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith
  intro C hC degree
  let A : ℝ := C + 2 * (degree : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hd : 0 ≤ (degree : ℝ) := Nat.cast_nonneg degree
    linarith
  have hM : 0 ≤ B * (A + 2) :=
    mul_nonneg (le_of_lt hB) (by linarith)
  filter_upwards [hPhysical (B * (A + 2)) hM] with n hn
  have hOriginal : (1 : ℝ) ≤ (k (l (q n)) : ℝ) + 1 := by
    have hNat : 0 ≤ (k (l (q n)) : ℝ) := Nat.cast_nonneg _
    linarith
  have hPoly :
      C * ((k (l (q n)) : ℝ) + 1) ^ degree <
        Real.exp
          (Real.exp
            ((B * (A + 2)) *
              Real.sqrt ((k (l (q n)) : ℝ) + 1)) / B - 1) ^ 2 :=
    polynomial_lt_endpointScale C B
      ((k (l (q n)) : ℝ) + 1) degree hC hB hOriginal
  exact hPoly.trans_le (le_min hn.1 hn.2)

end

end Euclidean
end Bridge
end PrimeTensor
