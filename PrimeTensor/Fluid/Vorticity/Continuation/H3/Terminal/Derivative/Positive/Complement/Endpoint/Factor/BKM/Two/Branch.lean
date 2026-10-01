import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Double.Exponential.Frequency

/-!
# Two growth mechanisms on the persistent endpoint witness

The exponential vorticity-factor branch already implies divergence
of its squared factor normalized by the original index. Thus the
three persistent outcomes reduce to a normalized vorticity-rate
branch or a double-exponential characteristic-frequency branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem normalizedSquare_atTop_of_exponentialBarrier
    (k : ℕ → ℕ) (A : ℕ → ℝ) (D : ℝ)
    (hDPos : 0 < D)
    (hBarrier : ∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (M * Real.sqrt ((k n : ℝ) + 1)) ^ 2 <
        D * (A n) ^ 2) :
    Tendsto (fun n : ℕ => (A n) ^ 2 / ((k n : ℝ) + 1))
      atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro C
  let C₀ : ℝ := max C 0
  let M : ℝ := D * (C₀ + 1) + 1
  have hC₀Nonneg : 0 ≤ C₀ := le_max_right C 0
  have hMNonneg : 0 ≤ M := by
    dsimp [M]
    have hProduct := mul_nonneg (le_of_lt hDPos)
      (by linarith : 0 ≤ C₀ + 1)
    linarith
  have hDC : D * C ≤ 2 * M ^ 2 := by
    have hCLe : C ≤ C₀ := le_max_left C 0
    have hFirst : D * C ≤ D * C₀ :=
      mul_le_mul_of_nonneg_left hCLe (le_of_lt hDPos)
    have hSecond : D * C₀ ≤ 2 * M ^ 2 := by
      dsimp [M]
      have hProduct : 0 ≤ D * (C₀ + 1) :=
        mul_nonneg (le_of_lt hDPos) (by linarith)
      have hLe : D * C₀ ≤ D * (C₀ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hDPos)
      nlinarith [sq_nonneg (D * (C₀ + 1))]
    exact hFirst.trans hSecond
  filter_upwards [hBarrier M hMNonneg] with n hn
  have hDenPos : 0 < (k n : ℝ) + 1 := by positivity
  have hSqrtNonneg : 0 ≤ Real.sqrt ((k n : ℝ) + 1) :=
    Real.sqrt_nonneg _
  have hArgumentNonneg :
      0 ≤ M * Real.sqrt ((k n : ℝ) + 1) :=
    mul_nonneg hMNonneg hSqrtNonneg
  have hExpBound :
      M * Real.sqrt ((k n : ℝ) + 1) ≤
        Real.exp (M * Real.sqrt ((k n : ℝ) + 1)) := by
    linarith [Real.add_one_le_exp
      (M * Real.sqrt ((k n : ℝ) + 1))]
  have hSquareBound :
      M ^ 2 * ((k n : ℝ) + 1) ≤
        Real.exp (M * Real.sqrt ((k n : ℝ) + 1)) ^ 2 := by
    have hSquare :=
      (sq_le_sq₀ hArgumentNonneg
        (le_of_lt (Real.exp_pos _))).2 hExpBound
    calc
      _ = (M * Real.sqrt ((k n : ℝ) + 1)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hDenPos)]
      _ ≤ _ := hSquare
  have hDProduct : D * (C * ((k n : ℝ) + 1)) ≤
      D * (A n) ^ 2 := by
    calc
      _ = (D * C) * ((k n : ℝ) + 1) := by ring
      _ ≤ (2 * M ^ 2) * ((k n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hDC (le_of_lt hDenPos)
      _ ≤ 2 * Real.exp (M * Real.sqrt ((k n : ℝ) + 1)) ^ 2 := by
        nlinarith [hSquareBound]
      _ ≤ D * (A n) ^ 2 := le_of_lt hn
  apply (le_div_iff₀ hDenPos).2
  by_contra hNot
  have hStrict : (A n) ^ 2 < C * ((k n : ℝ) + 1) :=
    lt_of_not_ge hNot
  exact (not_lt_of_ge hDProduct)
    (mul_lt_mul_of_pos_left hStrict hDPos)

/-- The refined native relative-escape witness has two growth
mechanisms: normalized vorticity-factor escape or the explicit
double-exponential frequency scale. -/
theorem endpointFactor_relativeRefinedWitness_BKMTwoBranch
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
        (∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
          Real.exp
            (Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) /
              (h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1) - 1) ≤
            h3TopCharacteristicFrequencyAt u (τ (k (l (q n)))))) := by
  obtain ⟨l, q, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMDoubleExponentialFrequency
      hH3 hNoExtension hClass hb hg hWitness
  rcases hBranches with hVorticity | hOther
  · exact ⟨l, q, hqIndex, hNative, hRatio, Or.inl hVorticity⟩
  rcases hOther with hExpVorticity | hFrequency
  · have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b
    have hCPos : 0 < 4 + 3 * velocityH3Energy0At u b := by
      linarith
    have hBNonneg :
        0 ≤ h3BKMCanonicalSelectedLogGradientConstant
          (Real.sqrt (velocityH3Energy0At u b)) :=
      h3BKMCanonicalSelectedLogGradientConstant_nonneg
        (Real.sqrt_nonneg _)
    have hDPos : 0 <
        (4 + 3 * velocityH3Energy0At u b) *
          (4422 *
            (h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt (velocityH3Energy0At u b)) + 1)) :=
      mul_pos hCPos
        (mul_pos (by norm_num) (by linarith))
    have hBarrier : ∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
        2 * Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) ^ 2 <
          ((4 + 3 * velocityH3Energy0At u b) *
            (4422 *
              (h3BKMCanonicalSelectedLogGradientConstant
                (Real.sqrt (velocityH3Energy0At u b)) + 1))) *
            (1 + |g (τ (k (l (q n))))|) ^ 2 := by
      intro M hM
      filter_upwards [hExpVorticity M hM] with n hn
      calc
        _ < (4 + 3 * velocityH3Energy0At u b) *
            (4422 *
              (h3BKMCanonicalSelectedLogGradientConstant
                (Real.sqrt (velocityH3Energy0At u b)) + 1) *
              (1 + |g (τ (k (l (q n))))|) ^ 2) := hn
        _ = _ := by ring
    exact ⟨l, q, hqIndex, hNative, hRatio,
      Or.inl (normalizedSquare_atTop_of_exponentialBarrier
        (fun n => k (l (q n)))
        (fun n => 1 + |g (τ (k (l (q n))))|)
        ((4 + 3 * velocityH3Energy0At u b) *
          (4422 *
            (h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt (velocityH3Energy0At u b)) + 1)))
        hDPos hBarrier)⟩
  · exact ⟨l, q, hqIndex, hNative, hRatio, Or.inr hFrequency⟩

end

end Euclidean
end Bridge
end PrimeTensor
