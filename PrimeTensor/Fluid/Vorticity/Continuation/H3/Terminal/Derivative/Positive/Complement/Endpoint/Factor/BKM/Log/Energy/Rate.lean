import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Transport.Shares
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Exponential.Barrier

/-!
# Logarithmic energy rate under a bounded vorticity factor

The physical endpoint branch has superpolynomial normalized dissipation.
If its normalized vorticity factor is bounded, the BKM product estimate
forces the remaining logarithmic energy factor to outrun every polynomial
of the original index on the same witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- If a rate outruns every power of a scale, and it is eventually at
most a fixed positive multiple of the scale times another factor, then
that factor also outruns every power. -/
theorem superpolynomial_factor_of_linear_product_bound
    (D L scale : ℕ → ℝ) (A : ℝ)
    (hA : 0 < A)
    (hScale : ∀ n, 1 ≤ scale n)
    (hD : ∀ degree : ℕ,
      Tendsto (fun n => D n / scale n ^ degree) atTop atTop)
    (hBound : ∀ᶠ n : ℕ in atTop, D n ≤ A * scale n * L n) :
    ∀ degree : ℕ,
      Tendsto (fun n => L n / scale n ^ degree) atTop atTop := by
  intro degree
  refine tendsto_atTop.2 ?_
  intro C
  have hLarge := (hD (degree + 1)).eventually
    (eventually_gt_atTop (A * max C 0))
  filter_upwards [hLarge, hBound] with n hnLarge hnBound
  have hs : 0 < scale n := lt_of_lt_of_le zero_lt_one (hScale n)
  have hp : 0 < scale n ^ degree := pow_pos hs _
  have hpNext : 0 < scale n ^ (degree + 1) := pow_pos hs _
  have hDLower :
      A * max C 0 * scale n ^ (degree + 1) < D n :=
    (lt_div_iff₀ hpNext).mp hnLarge
  have hLLower : max C 0 * scale n ^ degree < L n := by
    by_contra hNot
    have hUp : L n ≤ max C 0 * scale n ^ degree := le_of_not_gt hNot
    have hScaled := mul_le_mul_of_nonneg_left hUp
      (mul_nonneg hA.le hs.le)
    have hPower :
        A * max C 0 * scale n ^ (degree + 1) =
          A * scale n * (max C 0 * scale n ^ degree) := by
      rw [pow_succ]
      ring
    have hImpossible :
        A * max C 0 * scale n ^ (degree + 1) <
          A * max C 0 * scale n ^ (degree + 1) := by
      calc
        _ < D n := hDLower
        _ ≤ A * scale n * L n := hnBound
        _ ≤ A * scale n * (max C 0 * scale n ^ degree) := hScaled
        _ = _ := hPower.symm
    exact (lt_irrefl _) hImpossible
  have hDiv : max C 0 < L n / scale n ^ degree :=
    (lt_div_iff₀ hp).2 hLLower
  exact (le_max_left C 0).trans (le_of_lt hDiv)

/-- On the physical branch chosen by polynomial energy growth and a
bounded normalized vorticity factor, the logarithmic H³ energy factor
is superpolynomial on the original index. The prior native witness and
the adverse-transport shares are retained. -/
theorem endpointFactor_relativeRefinedWitness_logEnergySuperpolynomial
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
        atTop (𝓝 ((1 : ℝ) / 2)) ∧
      (∀ degree : ℕ,
        Tendsto
          (fun n : ℕ =>
            (1 + Real.log (velocityH3EnergyAt u (τ (k (l (r n)))))) /
              (((k (l (r n)) : ℝ) + 1) ^ degree))
          atTop atTop) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio,
      hPhysical, hGrowthShare, hExcessShare⟩ :=
    endpointFactor_relativeRefinedWitness_transportShares
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio,
    hPhysical, hGrowthShare, hExcessShare, ?_⟩
  let K : ℝ := 4422 *
    (h3BKMCanonicalSelectedLogGradientConstant
      (Real.sqrt (velocityH3Energy0At u b)) + 1)
  let A : ℝ := K * (max B 0 + 1)
  have hKNonneg : 0 ≤ h3BKMCanonicalSelectedLogGradientConstant
      (Real.sqrt (velocityH3Energy0At u b)) :=
    h3BKMCanonicalSelectedLogGradientConstant_nonneg (Real.sqrt_nonneg _)
  have hK : 0 < K := by
    dsimp [K]
    nlinarith
  have hA : 0 < A :=
    mul_pos hK (by have := le_max_right B 0; linarith)
  have hScale : ∀ n : ℕ, 1 ≤ (k (l (r n)) : ℝ) + 1 := by
    intro n
    have hn : 0 ≤ (k (l (r n)) : ℝ) := Nat.cast_nonneg _
    linarith
  have hDTop := (hNative.2.2.2.1).eventually (eventually_gt_atTop (0 : ℝ))
  have hVort := hIndex.eventually hVorticityCeiling
  have hBKM := positiveGrowth_nativeWitness_dissipation_le_canonicalBKM
    hH3 hClass hb hg hNative
  have hBound : ∀ᶠ n : ℕ in atTop,
      velocityH3DissipationAt u (τ (k (l (r n)))) /
          velocityH3EnergyAt u (τ (k (l (r n)))) ≤
        A * ((k (l (r n)) : ℝ) + 1) *
          (1 + Real.log (velocityH3EnergyAt u (τ (k (l (r n)))))) := by
    filter_upwards [hDTop, hVort] with n hnD hnVort
    let S : ℝ := (k (l (r n)) : ℝ) + 1
    let V : ℝ := 1 + |g (τ (k (l (r n))))|
    let L : ℝ := 1 + Real.log (velocityH3EnergyAt u (τ (k (l (r n)))))
    have hS : 0 < S := lt_of_lt_of_le zero_lt_one (hScale n)
    have hSquare : V ^ 2 ≤ B * S := (div_le_iff₀ hS).mp hnVort
    have hVOne : 1 ≤ V := by
      dsimp [V]
      have := abs_nonneg (g (τ (k (l (r n)))))
      linarith
    have hVLeSq : V ≤ V ^ 2 := by
      calc
        V = V * 1 := by ring
        _ ≤ V * V := mul_le_mul_of_nonneg_left hVOne (by linarith)
        _ = V ^ 2 := by ring
    have hVBound : V ≤ (max B 0 + 1) * S := by
      calc
        V ≤ V ^ 2 := hVLeSq
        _ ≤ B * S := hSquare
        _ ≤ max B 0 * S :=
          mul_le_mul_of_nonneg_right (le_max_left B 0) hS.le
        _ ≤ (max B 0 + 1) * S :=
          mul_le_mul_of_nonneg_right (by linarith) hS.le
    have hLNonneg : 0 ≤ L := by
      dsimp [L]
      have hEnergy := one_le_velocityH3EnergyAt u (τ (k (l (r n))))
      have hLog := Real.log_nonneg hEnergy
      linarith
    have hScaled : K * V * L ≤ K * ((max B 0 + 1) * S) * L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hVBound hK.le) hLNonneg
    calc
      velocityH3DissipationAt u (τ (k (l (r n)))) /
          velocityH3EnergyAt u (τ (k (l (r n)))) ≤
        2 * (velocityH3DissipationAt u (τ (k (l (r n)))) /
          velocityH3EnergyAt u (τ (k (l (r n))))) := by linarith
      _ ≤ K * V * L := le_of_lt (hBKM n)
      _ ≤ K * ((max B 0 + 1) * S) * L := hScaled
      _ = A * S * L := by dsimp [A]; ring
  exact superpolynomial_factor_of_linear_product_bound
    (fun n =>
      velocityH3DissipationAt u (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n)))))
    (fun n => 1 + Real.log (velocityH3EnergyAt u (τ (k (l (r n))))))
    (fun n => (k (l (r n)) : ℝ) + 1)
    A hA hScale (fun degree => (hPhysical.1 degree).1) hBound

end

end Euclidean
end Bridge
end PrimeTensor
