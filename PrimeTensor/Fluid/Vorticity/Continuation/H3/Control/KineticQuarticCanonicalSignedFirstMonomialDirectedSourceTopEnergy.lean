import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceEnergyGrowth

/-!
# Fixed signed H3 source synchronizes the actual third-derivative energy

The earlier Landau source ceiling was weakened from E3 to full E. Retaining
E3 proves a strictly stronger necessary consequence of hypothetical H3
nonextension: the *same* selected directed-source witness sequence has
E3(tau n) -> +infinity, and quantitatively

    n * sqrt(E(tau n)) < 324 * C1 * E3(tau n)

eventually. No new PDE regularity or unconditional continuation is claimed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Keep the third-order physical energy in the Landau upper bound, rather
than substituting `E3 <= E`. All ten directed sources are included. -/
theorem h3PathCanonical_directedTenSource_le_landauThirdEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 10) :
    h3PathCanonicalJointDirectedTenSourceAt u t i ≤
      2916 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t := by
  let H : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt (velocityH3EnergyAt u t)
  let E₃ : ℝ := velocityH3Energy3At u t
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact mul_nonneg
      (le_of_lt h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos)
      (Real.sqrt_nonneg _)
  have hE₃ : 0 ≤ E₃ := velocityH3Energy3At_nonneg u t
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hProduct : 0 ≤ H * E₃ := mul_nonneg hH hE₃
  have hGradient :
      24 * H * E₃ - velocityH3DissipationAt u t ≤ 2916 * H * E₃ := by
    nlinarith only [hD, hProduct]
  have hDirected (j r : PrimeTensor.Axis Depth.three) :
      -(18 * h3PathCanonicalFirstMonomialComponentAt u t j r) ≤
        2916 * H * E₃ := by
    have hAbs :
        |h3PathCanonicalFirstMonomialComponentAt u t j r| ≤ 162 * H * E₃ := by
      simpa only [H, E₃] using
        h3PathCanonical_abs_directedComponent_le_landau hH3 hClass ht j r
    have hNeg := neg_le_abs (h3PathCanonicalFirstMonomialComponentAt u t j r)
    nlinarith only [hAbs, hNeg]
  have hDiagonal (j r : PrimeTensor.Axis Depth.three) :
      -(9 * h3PathCanonicalFirstMonomialComponentAt u t j r) ≤
        2916 * H * E₃ := by
    have hAbs :
        |h3PathCanonicalFirstMonomialComponentAt u t j r| ≤ 162 * H * E₃ := by
      simpa only [H, E₃] using
        h3PathCanonical_abs_directedComponent_le_landau hH3 hClass ht j r
    have hNeg := neg_le_abs (h3PathCanonicalFirstMonomialComponentAt u t j r)
    nlinarith only [hAbs, hNeg, hProduct]
  fin_cases i
  · change 24 * H * E₃ - velocityH3DissipationAt u t ≤ 2916 * H * E₃
    exact hGradient
  · change -(9 * h3PathCanonicalFirstMonomialComponentAt u t xAxis xAxis) ≤ 2916 * H * E₃
    exact hDiagonal xAxis xAxis
  · change -(9 * h3PathCanonicalFirstMonomialComponentAt u t yAxis yAxis) ≤ 2916 * H * E₃
    exact hDiagonal yAxis yAxis
  · change -(9 * h3PathCanonicalFirstMonomialComponentAt u t zAxis zAxis) ≤ 2916 * H * E₃
    exact hDiagonal zAxis zAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t xAxis yAxis) ≤ 2916 * H * E₃
    exact hDirected xAxis yAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t yAxis xAxis) ≤ 2916 * H * E₃
    exact hDirected yAxis xAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t xAxis zAxis) ≤ 2916 * H * E₃
    exact hDirected xAxis zAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t zAxis xAxis) ≤ 2916 * H * E₃
    exact hDirected zAxis xAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t yAxis zAxis) ≤ 2916 * H * E₃
    exact hDirected yAxis zAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t zAxis yAxis) ≤ 2916 * H * E₃
    exact hDirected zAxis yAxis

/-- Under hypothetical nonextension, one fixed directed source has a terminal
sequence on which both its normalized value and the *top derivative energy*
diverge. The quantitative top-energy inequality holds eventually on that
same sequence, not along a separately chosen E3 blowup sequence. -/
theorem h3PathCanonical_fixedDirectedSource_thirdEnergyBlowup_sameSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ,
        τ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ =>
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) atTop atTop ∧
      (∀ᶠ n : ℕ in atTop,
        (n : ℝ) * Real.sqrt (velocityH3EnergyAt u (τ n)) <
          324 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            velocityH3Energy3At u (τ n)) ∧
      Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n)) atTop atTop := by
  obtain ⟨i, τ, hWitness, hτT, hRatioT, _hRawT⟩ :=
    h3PathCanonical_fixedDirectedTenSource_normalizedTerminalSequence
      hH3 hNoExtension hClass hb
  let C : ℝ := 324 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by norm_num)
      (le_of_lt h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos)
  have hLate : ∀ᶠ n : ℕ in atTop, b < τ n :=
    (tendsto_order.1 hτT).1 b hb.2
  have hRate : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.sqrt (velocityH3EnergyAt u (τ n)) <
        C * velocityH3Energy3At u (τ n) := by
    filter_upwards [hLate] with n hn
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hn, (hWitness n).1.2⟩
    have hUpper := h3PathCanonical_directedTenSource_le_landauThirdEnergy
      hH3 hClass ht i
    have hE : 0 < velocityH3EnergyAt u (τ n) :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u (τ n))
    have hRoot : 0 < Real.sqrt (velocityH3EnergyAt u (τ n)) :=
      Real.sqrt_pos.2 hE
    have hSquare :
        Real.sqrt (velocityH3EnergyAt u (τ n)) ^ 2 =
          velocityH3EnergyAt u (τ n) := Real.sq_sqrt hE.le
    have hDen : 0 < 9 * velocityH3EnergyAt u (τ n) := by
      positivity
    have hNum :
        (9 * (n : ℝ)) * velocityH3EnergyAt u (τ n) <
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i := by
      calc
        _ = (n : ℝ) * (9 * velocityH3EnergyAt u (τ n)) := by ring
        _ < _ := (lt_div_iff₀ hDen).mp (hWitness n).2
    have hFactor :
        (9 * (n : ℝ) * Real.sqrt (velocityH3EnergyAt u (τ n))) *
            Real.sqrt (velocityH3EnergyAt u (τ n)) <
          (2916 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            velocityH3Energy3At u (τ n)) *
            Real.sqrt (velocityH3EnergyAt u (τ n)) := by
      calc
        _ = (9 * (n : ℝ)) *
              Real.sqrt (velocityH3EnergyAt u (τ n)) ^ 2 := by ring
        _ = (9 * (n : ℝ)) * velocityH3EnergyAt u (τ n) := by
          rw [hSquare]
        _ < h3PathCanonicalJointDirectedTenSourceAt u (τ n) i := hNum
        _ ≤ 2916 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              Real.sqrt (velocityH3EnergyAt u (τ n))) *
              velocityH3Energy3At u (τ n) := hUpper
        _ = _ := by ring
    have hCancel :
        9 * (n : ℝ) * Real.sqrt (velocityH3EnergyAt u (τ n)) <
          2916 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            velocityH3Energy3At u (τ n) := by
      by_contra hNot
      have hLe :
          2916 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            velocityH3Energy3At u (τ n) ≤
              9 * (n : ℝ) * Real.sqrt (velocityH3EnergyAt u (τ n)) :=
        le_of_not_gt hNot
      have hScaled := mul_le_mul_of_nonneg_right hLe hRoot.le
      exact (not_lt_of_ge hScaled) hFactor
    dsimp only [C]
    nlinarith only [hCancel]
  have hTopN : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) < C * velocityH3Energy3At u (τ n) := by
    filter_upwards [hRate] with n hBound
    have hOne : 1 ≤ velocityH3EnergyAt u (τ n) :=
      one_le_velocityH3EnergyAt u (τ n)
    have hRootOne : (1 : ℝ) ≤ Real.sqrt (velocityH3EnergyAt u (τ n)) := by
      simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt hOne)
    have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hScaled := mul_le_mul_of_nonneg_left hRootOne hN
    have hNLe : (n : ℝ) ≤
        (n : ℝ) * Real.sqrt (velocityH3EnergyAt u (τ n)) := by
      simpa only [mul_one] using hScaled
    exact lt_of_le_of_lt hNLe hBound
  have hTopT :
      Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    let B : ℝ := C * max M 0
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt B
    have hNat : ∀ᶠ n : ℕ in atTop, B < (n : ℝ) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact lt_of_lt_of_le hN (by exact_mod_cast hn)
    filter_upwards [hTopN, hNat] with n hg hn
    by_contra hFail
    have hLess : velocityH3Energy3At u (τ n) < M := lt_of_not_ge hFail
    have hEmax : velocityH3Energy3At u (τ n) ≤ max M 0 :=
      le_trans (le_of_lt hLess) (le_max_left M 0)
    have hScaled :
        C * velocityH3Energy3At u (τ n) ≤ B := by
      exact mul_le_mul_of_nonneg_left hEmax hC
    exact (not_lt_of_ge hScaled) (lt_trans hn hg)
  refine ⟨i, τ, hWitness, hτT, hRatioT, ?_, hTopT⟩
  simpa only [C, mul_assoc] using hRate

end
end Euclidean
end Bridge
end PrimeTensor
