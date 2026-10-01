import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Raw.Excess.Exponential

/-!
# Removing the fixed anchor from endpoint exponential rates

The exponential bounds hold for every coefficient on the original-index
polynomial. Raising that coefficient by the positive fixed anchor absorbs
the anchor in front of a physical rate. This leaves unanchored lower bounds
on the same selected witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A larger exponential coefficient absorbs a fixed positive factor
when the polynomial scale is at least one. -/
theorem exponential_square_absorbs_fixed_anchor
    (A C s : ℝ) (hC : 0 < C) (hs : 1 ≤ s) :
    C * Real.exp (A * s) ^ 2 < Real.exp ((A + C) * s) ^ 2 := by
  have hCs : C ≤ C * s := by
    nlinarith
  have hExp : 1 + C ≤ Real.exp (C * s) := by
    linarith [Real.add_one_le_exp (C * s)]
  have hExpSq : Real.exp (C * s) ≤ Real.exp (C * s) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp (C * s) - 1)]
  have hAnchor : C < Real.exp (C * s) ^ 2 := by
    linarith
  have hAPos : 0 < Real.exp (A * s) ^ 2 :=
    pow_pos (Real.exp_pos _) _
  calc
    C * Real.exp (A * s) ^ 2 <
        Real.exp (C * s) ^ 2 * Real.exp (A * s) ^ 2 :=
      mul_lt_mul_of_pos_right hAnchor hAPos
    _ = Real.exp ((A + C) * s) ^ 2 := by
      rw [add_mul, Real.exp_add]
      ring

/-- Bounds at every exponential coefficient remain true after removing
a fixed positive multiplier from the physical rate. -/
theorem unanchored_exponential_square_rate
    (m : ℕ → ℕ) (R : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hRate : ∀ A : ℝ, ∀ degree : ℕ,
      ∀ᶠ n : ℕ in atTop,
        Real.exp (A * (((m n : ℝ) + 1) ^ degree)) ^ 2 < C * R n) :
    ∀ A : ℝ, ∀ degree : ℕ,
      ∀ᶠ n : ℕ in atTop,
        Real.exp (A * (((m n : ℝ) + 1) ^ degree)) ^ 2 < R n := by
  intro A degree
  filter_upwards [hRate (A + C) degree] with n hn
  have hScaleOne : 1 ≤ (m n : ℝ) + 1 := by
    have hNonneg : 0 ≤ (m n : ℝ) := Nat.cast_nonneg _
    linarith
  have hPowerOne : 1 ≤ ((m n : ℝ) + 1) ^ degree :=
    one_le_pow₀ hScaleOne
  have hAbsorb :=
    exponential_square_absorbs_fixed_anchor
      A C (((m n : ℝ) + 1) ^ degree) hC hPowerOne
  exact lt_of_mul_lt_mul_left (hAbsorb.trans hn) hC.le

/-- Raw growth plus dissipation and the raw adverse-transport balance gap
both exceed every fixed exponential polynomial square without an anchor. -/
theorem endpointFactor_relativeRefinedWitness_unanchoredExponentialRates
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
      (∀ A : ℝ, ∀ degree : ℕ,
        ∀ᶠ n : ℕ in atTop,
          Real.exp (A * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
            deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) +
              velocityH3DissipationAt u (τ (k (l (r n)))) ∧
          Real.exp (A * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
            (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) -
              deriv (velocityH3EnergyAt u) (τ (k (l (r n))))) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, hRates⟩ :=
    endpointFactor_relativeRefinedWitness_rawExcessExponential
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, hPhysical, ?_⟩
  let anchor : ℝ := 4 + 3 * velocityH3Energy0At u b
  have hAnchorPos : 0 < anchor := by
    dsimp [anchor]
    have hE0 := velocityH3Energy0At_nonneg u b
    linarith
  have hRaw : ∀ A : ℝ, ∀ degree : ℕ,
      ∀ᶠ n : ℕ in atTop,
        Real.exp (A * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
          anchor * (deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) +
            velocityH3DissipationAt u (τ (k (l (r n))))) := by
    intro A degree
    exact (hRates A degree).mono (fun n hn => hn.1)
  have hGap : ∀ A : ℝ, ∀ degree : ℕ,
      ∀ᶠ n : ℕ in atTop,
        Real.exp (A * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
          anchor * ((-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) -
            deriv (velocityH3EnergyAt u) (τ (k (l (r n))))) := by
    intro A degree
    filter_upwards [hRates A degree] with n hn
    have hPos :
        0 < Real.exp (A * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 :=
      pow_pos (Real.exp_pos _) _
    dsimp [anchor]
    linarith [hn.2]
  have hRawUnanchored :=
    unanchored_exponential_square_rate
      (fun n => k (l (r n)))
      (fun n => deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) +
        velocityH3DissipationAt u (τ (k (l (r n)))))
      anchor hAnchorPos hRaw
  have hGapUnanchored :=
    unanchored_exponential_square_rate
      (fun n => k (l (r n)))
      (fun n => (-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) -
        deriv (velocityH3EnergyAt u) (τ (k (l (r n)))))
      anchor hAnchorPos hGap
  intro A degree
  filter_upwards [hRawUnanchored A degree, hGapUnanchored A degree]
    with n hnRaw hnGap
  exact ⟨hnRaw, hnGap⟩

end

end Euclidean
end Bridge
end PrimeTensor
