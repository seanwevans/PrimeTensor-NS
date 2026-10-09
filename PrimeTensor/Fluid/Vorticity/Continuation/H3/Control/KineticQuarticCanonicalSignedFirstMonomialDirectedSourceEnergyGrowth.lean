import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceTerminalSequence
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Total.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Absorption.Landau.Harmonic.Rate

/-!
# Landau bounds synchronize the fixed directed signed obstruction with H³ energy

The previous cofinal theorem fixes one of ten signed sources and obtains a
sequence τ(n) → T on which its normalization by 9 E grows beyond n.

The already-closed whole-space Landau/Hölder monomial estimate controls each
physical type-0 pairing by 6 C₁ sqrt(E) E₃. There are 27 derivative triples
in each ordered velocity-component entry Q(j,r), so

  |Q(j,r)| ≤ 162 C₁ sqrt(E) E₃.

The directed source weighting uses at most 18, yielding for all ten sources

  S_i ≤ 2916 C₁ sqrt(E) E₃ ≤ 2916 C₁ sqrt(E) E.

Thus the *same* signed-source sequence forces n < 324 C₁ sqrt(E(τ(n)))
eventually, and E(τ(n)) → +∞. This is a conditional necessary consequence
of nonextension and the proved Landau estimates. It neither rules out the
source nor proves singularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable local instance axisFintypeH3DirectedSourceEnergyGrowth
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable section

private theorem h3PathCanonical_abs_threeAxisSum_le_27
    (f : PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three → ℝ)
    (C : ℝ)
    (h : ∀ i k l, |f i k l| ≤ C) :
    |∑ i : PrimeTensor.Axis Depth.three,
       ∑ k : PrimeTensor.Axis Depth.three,
         ∑ l : PrimeTensor.Axis Depth.three, f i k l| ≤ 27 * C := by
  classical
  calc
    _ ≤ ∑ i : PrimeTensor.Axis Depth.three,
        |∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three, f i k l| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            |∑ l : PrimeTensor.Axis Depth.three, f i k l| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three, |f i k l| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three, C := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      exact h i k l
    _ = 27 * C := by
      simp only [axis_sum_three]
      ring

/-- Actual Landau/Hölder bound for any ordered velocity-component channel:
all 27 signed monomials are controlled independently; no sign is presumed. -/
theorem h3PathCanonical_abs_directedComponent_le_landau
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j r : PrimeTensor.Axis Depth.three) :
    |h3PathCanonicalFirstMonomialComponentAt u t j r| ≤
      162 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t := by
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hGradient : VelocityGradientEnvelope u h t := by
    simpa only [h] using
      h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have htAbsolute : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hH3At : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbsolute
  have hSobolev6 : WholeSpaceC1H1ToL6 :=
    wholeSpaceC1H1ToL6_of_fderiv wholeSpaceC1FDerivL2ToL6_cutoff
  have hSobolev4 : WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6 hSobolev6
  have hCore : H3OrderThreeInterpolationLandauCoreAnalyticDataAt u h t := by
    simpa [H3OrderThreeInterpolationLandauCoreAnalyticDataAt] using hGradient
  have hAnalytic : H3OrderThreeInterpolationLandauAnalyticDataAt u h t :=
    h3OrderThreeInterpolationLandauAnalyticDataAt_of_core
      hSobolev4 wholeSpaceQuarticDerivativeIntegrationByParts_cutoff
      hClass ht hH3At hCore
  have hMono : H3OrderThreeInterpolationMonomialEstimateAt u h t 6 :=
    h3OrderThreeInterpolationMonomialEstimateAt_of_holderLandau
      (h3OrderThreeInterpolationHolderLandauAt_of_analyticData hAnalytic)
  have hTerm (i k l : PrimeTensor.Axis Depth.three) :
      |h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0| ≤
        6 * h t * velocityH3Energy3At u t := by
    simpa [h3PathCanonicalInterpolationMonomialPairing] using
      (hMono.2 i k l j r).1
  unfold h3PathCanonicalFirstMonomialComponentAt
  have hSum := h3PathCanonical_abs_threeAxisSum_le_27
    (fun i k l => h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0)
    (6 * h t * velocityH3Energy3At u t) hTerm
  simpa only [h, h3PathCanonicalSqrtEnergyGradientEnvelope] using
    (show |∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0| ≤
      162 * (h t) * velocityH3Energy3At u t from by
        nlinarith only [hSum])

/-- Every one of the ten actual signed sources is bounded *above* by the
existing physical Landau estimate; this is not a gradient absorption claim. -/
theorem h3PathCanonical_directedTenSource_le_landauEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 10) :
    h3PathCanonicalJointDirectedTenSourceAt u t i ≤
      2916 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t := by
  let H : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt (velocityH3EnergyAt u t)
  let E₃ : ℝ := velocityH3Energy3At u t
  let E : ℝ := velocityH3EnergyAt u t
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact mul_nonneg
      (le_of_lt h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos)
      (Real.sqrt_nonneg _)
  have hE₃ : 0 ≤ E₃ := velocityH3Energy3At_nonneg u t
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hE₃le : E₃ ≤ E := velocityH3Energy3At_le_velocityH3EnergyAt u t
  have hProduct : 0 ≤ H * E₃ := mul_nonneg hH hE₃
  have hProductLe : H * E₃ ≤ H * E :=
    mul_le_mul_of_nonneg_left hE₃le hH
  have hGradient :
      24 * H * E₃ - velocityH3DissipationAt u t ≤ 2916 * H * E := by
    nlinarith only [hD, hProduct, hProductLe]
  have hDirected (j r : PrimeTensor.Axis Depth.three) :
      -(18 * h3PathCanonicalFirstMonomialComponentAt u t j r) ≤
        2916 * H * E := by
    have hAbs :
        |h3PathCanonicalFirstMonomialComponentAt u t j r| ≤ 162 * H * E₃ := by
      simpa only [H, E₃] using
        h3PathCanonical_abs_directedComponent_le_landau hH3 hClass ht j r
    have hNeg := neg_le_abs (h3PathCanonicalFirstMonomialComponentAt u t j r)
    nlinarith only [hAbs, hNeg, hProductLe]
  have hDiagonal (j r : PrimeTensor.Axis Depth.three) :
      -(9 * h3PathCanonicalFirstMonomialComponentAt u t j r) ≤
        2916 * H * E := by
    have hAbs :
        |h3PathCanonicalFirstMonomialComponentAt u t j r| ≤ 162 * H * E₃ := by
      simpa only [H, E₃] using
        h3PathCanonical_abs_directedComponent_le_landau hH3 hClass ht j r
    have hNeg := neg_le_abs (h3PathCanonicalFirstMonomialComponentAt u t j r)
    nlinarith only [hAbs, hNeg, hProductLe, hProduct]
  fin_cases i
  · change 24 * H * E₃ - velocityH3DissipationAt u t ≤ 2916 * H * E
    exact hGradient
  · change -(9 * h3PathCanonicalFirstMonomialComponentAt u t xAxis xAxis) ≤ 2916 * H * E
    exact hDiagonal xAxis xAxis
  · change -(9 * h3PathCanonicalFirstMonomialComponentAt u t yAxis yAxis) ≤ 2916 * H * E
    exact hDiagonal yAxis yAxis
  · change -(9 * h3PathCanonicalFirstMonomialComponentAt u t zAxis zAxis) ≤ 2916 * H * E
    exact hDiagonal zAxis zAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t xAxis yAxis) ≤ 2916 * H * E
    exact hDirected xAxis yAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t yAxis xAxis) ≤ 2916 * H * E
    exact hDirected yAxis xAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t xAxis zAxis) ≤ 2916 * H * E
    exact hDirected xAxis zAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t zAxis xAxis) ≤ 2916 * H * E
    exact hDirected zAxis xAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t yAxis zAxis) ≤ 2916 * H * E
    exact hDirected yAxis zAxis
  · change -(18 * h3PathCanonicalFirstMonomialComponentAt u t zAxis yAxis) ≤ 2916 * H * E
    exact hDirected zAxis yAxis

/-- At the *same* fixed directed-source witness times, the H³ energy
must diverge. The shared sequence also has an explicit square-root energy
rate `n < 324 C₁ sqrt(E)`, eventually on the physical energy-class tail. -/
theorem h3PathCanonical_fixedDirectedSource_energyBlowup_sameSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ => h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
          (9 * velocityH3EnergyAt u (τ n))) atTop atTop ∧
      (∀ᶠ n : ℕ in atTop,
        (n : ℝ) < 324 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u (τ n))) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ n)) atTop atTop := by
  obtain ⟨i, τ, hWitness, hτT, hRatioT, hRawT⟩ :=
    h3PathCanonical_fixedDirectedTenSource_normalizedTerminalSequence
      hH3 hNoExtension hClass hb
  have hLate : ∀ᶠ n : ℕ in atTop, b < τ n :=
    (tendsto_order.1 hτT).1 b hb.2
  have hGrowth : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) < 324 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u (τ n)) := by
    filter_upwards [hLate] with n hn
    have ht : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hn, (hWitness n).1.2⟩
    have hBound := h3PathCanonical_directedTenSource_le_landauEnergy
      hH3 hClass ht i
    have hE : 0 < velocityH3EnergyAt u (τ n) :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u (τ n))
    have hDen : 0 < 9 * velocityH3EnergyAt u (τ n) := by
      positivity
    have hNum :
        (9 * (n : ℝ)) * velocityH3EnergyAt u (τ n) <
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i := by
      calc
        _ = (n : ℝ) * (9 * velocityH3EnergyAt u (τ n)) := by ring
        _ < _ := (lt_div_iff₀ hDen).mp (hWitness n).2
    have hProduct :
        (9 * (n : ℝ)) * velocityH3EnergyAt u (τ n) <
          (2916 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n)))) *
              velocityH3EnergyAt u (τ n) := by
      nlinarith only [hNum, hBound]
    have hCancel :
        9 * (n : ℝ) <
          2916 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n))) := by
      by_contra hNot
      have hLe :
          2916 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n))) ≤ 9 * (n : ℝ) :=
        le_of_not_gt hNot
      have hScaled := mul_le_mul_of_nonneg_right hLe hE.le
      exact (not_lt_of_ge hScaled) hProduct
    nlinarith only [hCancel]
  have hEnergyT :
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ n)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    let C : ℝ := 324 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
    let B : ℝ := C * Real.sqrt (max M 0)
    have hC : 0 ≤ C := by
      dsimp only [C]
      exact mul_nonneg (by norm_num)
        (le_of_lt h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos)
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt B
    have hNat : ∀ᶠ n : ℕ in atTop, B < (n : ℝ) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact lt_of_lt_of_le hN (by exact_mod_cast hn)
    filter_upwards [hGrowth, hNat] with n hg hn
    by_contra hFail
    have hLess : velocityH3EnergyAt u (τ n) < M := lt_of_not_ge hFail
    have hEmax : velocityH3EnergyAt u (τ n) ≤ max M 0 :=
      le_trans (le_of_lt hLess) (le_max_left M 0)
    have hSqrt := Real.sqrt_le_sqrt hEmax
    have hCmul :
        C * Real.sqrt (velocityH3EnergyAt u (τ n)) ≤ B := by
      exact mul_le_mul_of_nonneg_left hSqrt hC
    dsimp only [C, B] at hCmul hn
    nlinarith only [hg, hn, hCmul]
  exact ⟨i, τ, hτT, hRatioT, hGrowth, hEnergyT⟩

end
end Euclidean
end Bridge
end PrimeTensor
