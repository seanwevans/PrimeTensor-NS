import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Intrinsic.Frequency

/-!
# Double-exponential intrinsic frequency on the log-energy branch

The intrinsic logarithmic frequency factor is exponentially large in
the square root of the original index on its persistent branch.
Solving that logarithmic inequality gives a double-exponential lower
bound on the actual characteristic frequency, with a fixed explicit
coefficient determined by the BKM and energy anchors.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The fixed coefficient in the exponential BKM intrinsic-frequency
estimate, expressed once for its double-exponential consequence. -/
def h3TerminalBKMIntrinsicFrequencyCoefficient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b : ℝ) : ℝ :=
  (4 + 3 * velocityH3Energy0At u b) *
    (4422 *
      (h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u b)) + 1) *
      (((4 + 3 * velocityH3Energy0At u b) *
        (velocityH3Energy0At u b + 1) + 7) ^ 2))

private theorem doubleExponential_of_logSquareBarrier
    (k : ℕ → ℕ) (Λ : ℕ → ℝ) (D : ℝ)
    (hDNonneg : 0 ≤ D)
    (hΛTop : Tendsto Λ atTop atTop)
    (hBarrier : ∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (M * Real.sqrt ((k n : ℝ) + 1)) ^ 2 <
        D * (1 + Real.log (Λ n)) ^ 2)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp
        (Real.exp (M * Real.sqrt ((k n : ℝ) + 1)) / (D + 1) - 1) ≤
        Λ n := by
  have hDPlusPos : 0 < D + 1 := by linarith
  filter_upwards
      [hBarrier M hM,
        hΛTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn hΛOne
  let X : ℝ := Real.exp (M * Real.sqrt ((k n : ℝ) + 1))
  let F : ℝ := 1 + Real.log (Λ n)
  have hXNonneg : 0 ≤ X := le_of_lt (Real.exp_pos _)
  have hFNonneg : 0 ≤ F := by
    dsimp [F]
    have hLog := Real.log_nonneg hΛOne
    linarith
  have hXSq : X ^ 2 ≤ D * F ^ 2 := by
    dsimp only [X, F] at hn ⊢
    nlinarith [sq_nonneg (Real.exp (M * Real.sqrt ((k n : ℝ) + 1)))]
  have hDSq : D ≤ (D + 1) ^ 2 := by
    nlinarith [sq_nonneg D]
  have hFSq : D * F ^ 2 ≤ (D + 1) ^ 2 * F ^ 2 :=
    mul_le_mul_of_nonneg_right hDSq (sq_nonneg F)
  have hSquareBound : X ^ 2 ≤ ((D + 1) * F) ^ 2 := by
    calc
      _ ≤ D * F ^ 2 := hXSq
      _ ≤ (D + 1) ^ 2 * F ^ 2 := hFSq
      _ = ((D + 1) * F) ^ 2 := by ring
  have hLinear : X ≤ (D + 1) * F :=
    (sq_le_sq₀ hXNonneg
      (mul_nonneg (le_of_lt hDPlusPos) hFNonneg)).1 hSquareBound
  have hDiv : X / (D + 1) ≤ F := by
    apply (div_le_iff₀ hDPlusPos).2
    simpa only [mul_comm] using hLinear
  have hLogLower : X / (D + 1) - 1 ≤ Real.log (Λ n) := by
    dsimp only [F] at hDiv
    linarith
  calc
    Real.exp (X / (D + 1) - 1)
        ≤ Real.exp (Real.log (Λ n)) :=
          Real.exp_le_exp.mpr hLogLower
    _ = Λ n := Real.exp_log (by linarith)

/-- On a refined native relative-escape witness, either vorticity
carries its normalized rate, vorticity itself carries the exponential
scale, or the intrinsic characteristic frequency carries a
double-exponential square-root-index lower bound. -/
theorem endpointFactor_relativeRefinedWitness_BKMDoubleExponentialFrequency
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
          2 * Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) ^ 2 <
            (4 + 3 * velocityH3Energy0At u b) *
              (4422 *
                (h3BKMCanonicalSelectedLogGradientConstant
                  (Real.sqrt (velocityH3Energy0At u b)) + 1) *
                (1 + |g (τ (k (l (q n))))|) ^ 2)) ∨
        (∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
          Real.exp
            (Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) /
              (h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1) - 1) ≤
            h3TopCharacteristicFrequencyAt u (τ (k (l (q n)))))) := by
  obtain ⟨l, q, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMIntrinsicFrequency
      hH3 hNoExtension hClass hb hg hWitness
  rcases hBranches with hVorticity | hOther
  · exact ⟨l, q, hqIndex, hNative, hRatio, Or.inl hVorticity⟩
  rcases hOther with hExpVorticity | hExpFrequency
  · exact ⟨l, q, hqIndex, hNative, hRatio,
      Or.inr (Or.inl hExpVorticity)⟩
  have hΛTop : Tendsto
      (fun n : ℕ => h3TopCharacteristicFrequencyAt u
        (τ (k (l (q n))))) atTop atTop := by
    rcases hNative with ⟨_, _, _, _, _, hΛTop, _, _, _⟩
    exact hΛTop
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
  have hFrequencyBound : ∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) ^ 2 <
        h3TerminalBKMIntrinsicFrequencyCoefficient u b *
          (1 + Real.log
            (h3TopCharacteristicFrequencyAt u (τ (k (l (q n)))))) ^ 2 := by
    intro M hM
    filter_upwards [hExpFrequency M hM] with n hn
    calc
      _ < (4 + 3 * velocityH3Energy0At u b) *
          (4422 *
            (h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt (velocityH3Energy0At u b)) + 1) *
            (((4 + 3 * velocityH3Energy0At u b) *
              (velocityH3Energy0At u b + 1) + 7) ^ 2 *
              (1 + Real.log
                (h3TopCharacteristicFrequencyAt u
                  (τ (k (l (q n)))))) ^ 2)) := hn
      _ = h3TerminalBKMIntrinsicFrequencyCoefficient u b *
          (1 + Real.log
            (h3TopCharacteristicFrequencyAt u (τ (k (l (q n)))))) ^ 2 := by
        unfold h3TerminalBKMIntrinsicFrequencyCoefficient
        ring
  exact ⟨l, q, hqIndex, hNative, hRatio,
    Or.inr (Or.inr (fun M hM =>
      doubleExponential_of_logSquareBarrier
        (fun n => k (l (q n)))
        (fun n => h3TopCharacteristicFrequencyAt u (τ (k (l (q n)))))
        (h3TerminalBKMIntrinsicFrequencyCoefficient u b)
        hCoeffNonneg hΛTop hFrequencyBound M hM))⟩

end

end Euclidean
end Bridge
end PrimeTensor
