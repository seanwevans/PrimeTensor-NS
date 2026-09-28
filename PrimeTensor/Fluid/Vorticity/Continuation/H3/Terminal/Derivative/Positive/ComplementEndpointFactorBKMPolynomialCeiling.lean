import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMSingleExponentialCeiling

/-!
# Polynomial physical ceiling on the endpoint witness

Every fixed polynomial in the original extraction index is bounded
by a single exponential in its square root. The existing endpoint
ceiling theorem therefore forces normalized vorticity-factor escape
whenever the smaller physical rate has an eventual polynomial bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem polynomial_le_sqrtExponential
    (C x : ℝ) (p : ℕ) (hC : 0 ≤ C) (hx : 1 ≤ x) :
    C * x ^ p ≤
      Real.exp ((C + 2 * (p : ℝ)) * Real.sqrt x) := by
  let s := Real.sqrt x
  have hs : 1 ≤ s := by
    dsimp [s]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  have hSqrtSq : s ^ 2 = x := by
    dsimp [s]
    exact Real.sq_sqrt (by linarith)
  have hSExp : s ≤ Real.exp s := by
    linarith [Real.add_one_le_exp s]
  have hxExp : x ≤ Real.exp (2 * s) := by
    calc
      x = s ^ 2 := hSqrtSq.symm
      _ ≤ Real.exp s ^ 2 :=
        pow_le_pow_left₀ (by linarith : 0 ≤ s) hSExp 2
      _ = Real.exp (2 * s) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hPow : ∀ m : ℕ,
      x ^ m ≤ Real.exp (2 * (m : ℝ) * s) := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
      calc
        x ^ (m + 1) = x ^ m * x := by rw [pow_succ]
        _ ≤ Real.exp (2 * (m : ℝ) * s) * Real.exp (2 * s) :=
          mul_le_mul hm hxExp (by linarith) (le_of_lt (Real.exp_pos _))
        _ = Real.exp (2 * ((m + 1 : ℕ) : ℝ) * s) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
  have hCExp : C ≤ Real.exp (C * s) := by
    have hCS : C ≤ C * s := by
      nlinarith [mul_nonneg hC (by linarith : 0 ≤ s - 1)]
    linarith [Real.add_one_le_exp (C * s)]
  calc
    C * x ^ p ≤ Real.exp (C * s) * Real.exp (2 * (p : ℝ) * s) :=
      mul_le_mul hCExp (hPow p)
        (pow_nonneg (by linarith : 0 ≤ x) p)
        (le_of_lt (Real.exp_pos _))
    _ = Real.exp ((C + 2 * (p : ℝ)) * Real.sqrt x) := by
      dsimp [s]
      rw [← Real.exp_add]
      congr 1
      ring

/-- A fixed polynomial upper bound on the smaller anchored physical
rate of the original sequence selects the vorticity escape branch. -/
theorem endpointFactor_relativeRefinedWitness_vorticity_of_polynomialPhysicalBound
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
    (C : ℝ) (degree : ℕ) (hC : 0 ≤ C)
    (hPolynomial : ∀ᶠ j : ℕ in atTop,
      min
          ((4 + 3 * velocityH3Energy0At u b) *
            (velocityH3DissipationAt u (τ j) /
              velocityH3EnergyAt u (τ j)))
          ((4 + 3 * velocityH3Energy0At u b) *
            h3PathTransportExcessRate u (τ j)) ≤
        C * ((j : ℝ) + 1) ^ degree) :
    ∃ l q : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (q n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ q n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (q n)))) (fun n => y (k (l (q n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (q n))) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + |g (τ (k (l (q n))))|) ^ 2 /
            ((k (l (q n)) : ℝ) + 1))
        atTop atTop := by
  apply endpointFactor_relativeRefinedWitness_vorticity_of_singleExponentialPhysicalBound
    hH3 hNoExtension hClass hb hg hWitness
  refine ⟨C + 2 * (degree : ℝ), ?_, ?_⟩
  · have hDegree : 0 ≤ (degree : ℝ) := Nat.cast_nonneg degree
    linarith
  filter_upwards [hPolynomial] with j hj
  have hIndex : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    have hjNonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  exact hj.trans (polynomial_le_sqrtExponential C
    ((j : ℝ) + 1) degree hC hIndex)

end

end Euclidean
end Bridge
end PrimeTensor
