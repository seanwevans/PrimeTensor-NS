import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Product.Uniform.Integral.Error

/-!
# Exact weak-energy inequality from temporal product integrability

All pressure dependence has now been removed from the weak-energy route.

This file performs the final bookkeeping under the family-level temporal-product
integrability hypothesis:

* collapse the genuine uniform-mesh energy integrals;
* combine the inside-integral and endpoint/quadratic mesh errors;
* obtain the finite-mesh estimate
      ‖D(q)‖² ≤ 6 B(E) ∫₀^q ‖D(r)‖² dr
                + 24 ε C(E) q
                + 108 C(E)² q² / n;
* let `n → ∞`;
* let `ε → 0`.

The output is the exact Grönwall-ready relative-energy inequality with no
pressure mass or pressure continuity hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyProductExact
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The genuine energy part of the product-integrable uniform partition
telescopes exactly to the single interval `[0,q]`. -/
theorem sum_selectedOldDifference_uniformPartition_energyIntegral_eq_of_allTemporalProductIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hProduct :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (n : ℕ)
    (hn : 0 < n) :
    (∑ k ∈ Finset.range n,
      2 *
        (∫ r in
            ((k : ℝ) / (n : ℝ)) * q..
            (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q,
          3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail r‖ ^ 2))
      =
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      (∫ r in (0 : ℝ)..q,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2) := by
  let x : ℕ → ℝ :=
    fun k : ℕ => ((k : ℝ) / (n : ℝ)) * q

  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
      hNS ht hEnd hE hTail

  let F : ℝ → ℝ :=
    fun r : ℝ => ‖D r‖ ^ 2

  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hq0 : 0 ≤ q :=
    hq.1

  have hxmem :
      ∀ k : ℕ,
        k ≤ n →
          x k ∈ Set.Icc (0 : ℝ) tau := by
    intro k hk

    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by
      positivity

    have hkn : (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hk

    have hfrac0 :
        (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) :=
      div_nonneg hk0 (le_of_lt hnR)

    have hfrac1 :
        (k : ℝ) / (n : ℝ) ≤ 1 := by
      exact (div_le_one hnR).2 hkn

    have hx0 : 0 ≤ x k := by
      dsimp only [x]
      exact mul_nonneg hfrac0 hq0

    have hxq : x k ≤ q := by
      dsimp only [x]
      calc
        ((k : ℝ) / (n : ℝ)) * q
            ≤ 1 * q :=
          mul_le_mul_of_nonneg_right hfrac1 hq0
        _ = q := one_mul q

    exact ⟨hx0, hxq.trans hq.2⟩

  have hxmono :
      ∀ k : ℕ,
        k < n →
          x k ≤ x (k + 1) := by
    intro k _hk

    have hkSucc :
        (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_succ k)

    have hDiv :
        (k : ℝ) / (n : ℝ)
          ≤
        ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right hnR).2 hkSucc

    dsimp only [x]
    exact mul_le_mul_of_nonneg_right hDiv hq0

  have hDContTau :
      ContinuousOn D (Set.Icc (0 : ℝ) tau) := by
    dsimp only [D]
    exact
      continuousOn_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct

  have hFInt :
      ∀ k : ℕ,
        k < n →
          IntervalIntegrable F volume (x k) (x (k + 1)) := by
    intro k hk

    have hk_le : k ≤ n :=
      Nat.le_of_lt hk

    have hksucc_le : k + 1 ≤ n := by
      omega

    have hSub :
        Set.Icc (x k) (x (k + 1))
          ⊆
        Set.Icc (0 : ℝ) tau := by
      intro r hr
      exact
        ⟨
          (hxmem k hk_le).1.trans hr.1,
          hr.2.trans (hxmem (k + 1) hksucc_le).2
        ⟩

    have hFCont :
        ContinuousOn F (Set.Icc (x k) (x (k + 1))) := by
      dsimp only [F]
      exact
        (continuous_norm.comp_continuousOn
          (hDContTau.mono hSub)).pow 2

    exact
      hFCont.intervalIntegrable_of_Icc
        (hxmono k hk)

  have hAdj :
      (∑ k ∈ Finset.range n,
        ∫ r in x k..x (k + 1), F r)
        =
      ∫ r in x 0..x n, F r := by
    exact
      intervalIntegral.sum_integral_adjacent_intervals
        hFInt

  have hx0 : x 0 = 0 := by
    simp [x]

  have hxn : x n = q := by
    simp [x, ne_of_gt hnR]

  rw [hx0, hxn] at hAdj

  calc
    (∑ k ∈ Finset.range n,
      2 *
        (∫ r in
            ((k : ℝ) / (n : ℝ)) * q..
            (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q,
          3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail r‖ ^ 2))
        =
      ∑ k ∈ Finset.range n,
        (6 * h3PreterminalSelectedWeakStrongGradientEnvelope E) *
          (∫ r in x k..x (k + 1), F r) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [intervalIntegral.integral_const_mul]
            dsimp only [x, F, D]
            ring
    _ =
      (6 * h3PreterminalSelectedWeakStrongGradientEnvelope E) *
        (∑ k ∈ Finset.range n,
          ∫ r in x k..x (k + 1), F r) := by
            rw [Finset.mul_sum]
    _ =
      6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
        (∫ r in (0 : ℝ)..q, F r) := by
            rw [hAdj]
    _ =
      6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
        (∫ r in (0 : ℝ)..q,
          ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail r‖ ^ 2) := by
            rfl

/-- Finite uniform-mesh weak-energy inequality under only temporal product
integrability. -/
theorem norm_sq_selectedOldDifferenceReal_le_energyIntegral_add_uniformErrors_of_allTemporalProductIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q ε : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hProduct :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (n : ℕ)
    (hn : 0 < n)
    (hε : 0 < ε) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2
      ≤
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      (∫ r in (0 : ℝ)..q,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2)
      +
    24 * ε * h3UnitViscosityZeroRHSBound E * q
      +
    108 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2 / (n : ℝ) := by
  let x : ℕ → ℝ :=
    fun k : ℕ => ((k : ℝ) / (n : ℝ)) * q

  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
      hNS ht hEnd hE hTail

  let A : ℕ → ℝ → ℝ :=
    fun _k r =>
      3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
        ‖D r‖ ^ 2

  let B : ℕ → ℝ → ℝ :=
    fun k r =>
      (ε + ‖D (x k) - D r‖) *
        (6 * h3UnitViscosityZeroRHSBound E)

  let R : ℕ → ℝ :=
    fun k =>
      2 * ε * ‖D (x (k + 1)) - D (x k)‖
        +
      ‖D (x (k + 1)) - D (x k)‖ ^ 2

  have hPart :=
    norm_sq_selectedOldDifferenceReal_le_uniformPartitionApproximateEnergyIncrement_of_allTemporalProductIntegrable
      hNS ht htau hEnd hE hTail htauR hProduct
      hq n hn hε

  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hq0 : 0 ≤ q :=
    hq.1

  have hxmem :
      ∀ k : ℕ,
        k ≤ n →
          x k ∈ Set.Icc (0 : ℝ) tau := by
    intro k hk

    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by
      positivity

    have hkn : (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hk

    have hfrac0 :
        (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) :=
      div_nonneg hk0 (le_of_lt hnR)

    have hfrac1 :
        (k : ℝ) / (n : ℝ) ≤ 1 := by
      exact (div_le_one hnR).2 hkn

    have hx0 : 0 ≤ x k := by
      dsimp only [x]
      exact mul_nonneg hfrac0 hq0

    have hxq : x k ≤ q := by
      dsimp only [x]
      calc
        ((k : ℝ) / (n : ℝ)) * q
            ≤ 1 * q :=
          mul_le_mul_of_nonneg_right hfrac1 hq0
        _ = q := one_mul q

    exact ⟨hx0, hxq.trans hq.2⟩

  have hxmono :
      ∀ k : ℕ,
        k < n →
          x k ≤ x (k + 1) := by
    intro k _hk

    have hkSucc :
        (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_succ k)

    have hDiv :
        (k : ℝ) / (n : ℝ)
          ≤
        ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right hnR).2 hkSucc

    dsimp only [x]
    exact mul_le_mul_of_nonneg_right hDiv hq0

  have hDContTau :
      ContinuousOn D (Set.Icc (0 : ℝ) tau) := by
    dsimp only [D]
    exact
      continuousOn_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct

  have hSplit :
      ∀ k ∈ Finset.range n,
        2 *
            (∫ r in x k..x (k + 1),
              A k r + B k r)
          +
        R k
          =
        2 * (∫ r in x k..x (k + 1), A k r)
          +
        2 * (∫ r in x k..x (k + 1), B k r)
          +
        R k := by
    intro k hk

    have hklt : k < n :=
      Finset.mem_range.mp hk

    have hk_le : k ≤ n :=
      Nat.le_of_lt hklt

    have hksucc_le : k + 1 ≤ n := by
      omega

    have hSub :
        Set.Icc (x k) (x (k + 1))
          ⊆
        Set.Icc (0 : ℝ) tau := by
      intro r hr
      exact
        ⟨
          (hxmem k hk_le).1.trans hr.1,
          hr.2.trans (hxmem (k + 1) hksucc_le).2
        ⟩

    have hCellD :
        ContinuousOn D (Set.Icc (x k) (x (k + 1))) :=
      hDContTau.mono hSub

    have hACont :
        ContinuousOn
          (A k)
          (Set.Icc (x k) (x (k + 1))) := by
      dsimp only [A]
      exact
        continuousOn_const.mul
          ((continuous_norm.comp_continuousOn hCellD).pow 2)

    have hConstD :
        ContinuousOn
          (fun _r : ℝ => D (x k))
          (Set.Icc (x k) (x (k + 1))) :=
      continuousOn_const

    have hBCont :
        ContinuousOn
          (B k)
          (Set.Icc (x k) (x (k + 1))) := by
      dsimp only [B]
      exact
        (continuousOn_const.add
          (continuous_norm.comp_continuousOn
            (hConstD.sub hCellD))).mul
          continuousOn_const

    have hAInt :
        IntervalIntegrable
          (A k)
          volume
          (x k) (x (k + 1)) :=
      hACont.intervalIntegrable_of_Icc
        (hxmono k hklt)

    have hBInt :
        IntervalIntegrable
          (B k)
          volume
          (x k) (x (k + 1)) :=
      hBCont.intervalIntegrable_of_Icc
        (hxmono k hklt)

    rw [intervalIntegral.integral_add hAInt hBInt]
    ring

  have hSumSplit :
      (∑ k ∈ Finset.range n,
        (2 *
            (∫ r in x k..x (k + 1),
              A k r + B k r)
          +
        R k))
        =
      (∑ k ∈ Finset.range n,
        2 * (∫ r in x k..x (k + 1), A k r))
        +
      (∑ k ∈ Finset.range n,
        2 * (∫ r in x k..x (k + 1), B k r))
        +
      (∑ k ∈ Finset.range n, R k) := by
    calc
      (∑ k ∈ Finset.range n,
        (2 *
            (∫ r in x k..x (k + 1),
              A k r + B k r)
          +
        R k))
          =
        ∑ k ∈ Finset.range n,
          (2 * (∫ r in x k..x (k + 1), A k r)
            +
           2 * (∫ r in x k..x (k + 1), B k r)
            +
           R k) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact hSplit k hk
      _ =
        (∑ k ∈ Finset.range n,
          2 * (∫ r in x k..x (k + 1), A k r))
          +
        (∑ k ∈ Finset.range n,
          2 * (∫ r in x k..x (k + 1), B k r))
          +
        (∑ k ∈ Finset.range n, R k) := by
              simp only [Finset.sum_add_distrib]

  have hPartNamed :
      ‖D q‖ ^ 2
        ≤
      ∑ k ∈ Finset.range n,
        (2 *
            (∫ r in x k..x (k + 1),
              A k r + B k r)
          +
        R k) := by
    simpa only [x, D, A, B, R, add_assoc] using hPart

  have hPart' :
      ‖D q‖ ^ 2
        ≤
      (∑ k ∈ Finset.range n,
        2 * (∫ r in x k..x (k + 1), A k r))
        +
      (∑ k ∈ Finset.range n,
        2 * (∫ r in x k..x (k + 1), B k r))
        +
      (∑ k ∈ Finset.range n, R k) := by
    rw [hSumSplit] at hPartNamed
    exact hPartNamed

  have hEnergy :=
    sum_selectedOldDifference_uniformPartition_energyIntegral_eq_of_allTemporalProductIntegrable
      hNS ht htau hEnd hE hTail htauR hProduct
      hq n hn

  have hError :=
    sum_selectedOldDifference_uniformPartition_cellIntegralError_le_of_allTemporalProductIntegrable
      hNS ht htau hEnd hE hTail htauR hProduct
      hq n hn hε.le

  have hRemainder :=
    sum_selectedOldDifference_uniformPartition_endpointAndQuadratic_le_of_allTemporalProductIntegrable
      hNS ht htau hEnd hE hTail htauR hProduct
      hq n hn hε.le

  simp only [A, B, R, D, x] at hPart'

  rw [hEnergy] at hPart'

  calc
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2
        ≤
      6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
          (∫ r in (0 : ℝ)..q,
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail r‖ ^ 2)
        +
      (∑ k ∈ Finset.range n,
        2 *
          (∫ r in
              ((k : ℝ) / (n : ℝ)) * q..
              (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q,
            (ε +
              ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                    hNS ht hEnd hE hTail
                    (((k : ℝ) / (n : ℝ)) * q)
                -
                h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                    hNS ht hEnd hE hTail r‖)
              *
            (6 * h3UnitViscosityZeroRHSBound E)))
        +
      (∑ k ∈ Finset.range n,
        (2 * ε *
          ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail
                ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
            -
            h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail
                (((k : ℝ) / (n : ℝ)) * q)‖
          +
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail
              ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
          -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail
              (((k : ℝ) / (n : ℝ)) * q)‖ ^ 2)) := by
            simpa only [D, x, B, R] using hPart'
    _ ≤
      6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
          (∫ r in (0 : ℝ)..q,
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail r‖ ^ 2)
        +
      (12 * ε * h3UnitViscosityZeroRHSBound E * q
        +
       72 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2 / (n : ℝ))
        +
      (12 * ε * h3UnitViscosityZeroRHSBound E * q
        +
       36 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2 / (n : ℝ)) := by
            exact
              add_le_add
                (add_le_add_right hError _)
                hRemainder
    _ =
      6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
          (∫ r in (0 : ℝ)..q,
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail r‖ ^ 2)
        +
      24 * ε * h3UnitViscosityZeroRHSBound E * q
        +
      108 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2 / (n : ℝ) := by
            ring

/-- Remove the uniform mesh parameter under temporal product integrability. -/
theorem norm_sq_selectedOldDifferenceReal_le_energyIntegral_add_epsilonError_of_allTemporalProductIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q ε : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hProduct :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hε : 0 < ε) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2
      ≤
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      (∫ r in (0 : ℝ)..q,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2)
      +
    24 * ε * h3UnitViscosityZeroRHSBound E * q := by
  let A : ℝ :=
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2

  let M : ℝ :=
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      (∫ r in (0 : ℝ)..q,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2)
      +
    24 * ε * h3UnitViscosityZeroRHSBound E * q

  let K : ℝ :=
    108 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2

  have hInv :
      Tendsto
        (fun n : ℕ =>
          (1 : ℝ) / (((n + 1 : ℕ) : ℝ)))
        atTop
        (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hK :
      Tendsto
        (fun n : ℕ =>
          K / (((n + 1 : ℕ) : ℝ)))
        atTop
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _n : ℕ => K)
          atTop
          (𝓝 K) :=
      tendsto_const_nhds

    have hMul :=
      hConst.mul hInv

    simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using hMul

  have hRHS :
      Tendsto
        (fun n : ℕ =>
          M + K / (((n + 1 : ℕ) : ℝ)))
        atTop
        (𝓝 M) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add hK

  have hBound :
      ∀ᶠ n : ℕ in atTop,
        A
          ≤
        M + K / (((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [] with n

    have hFinite :=
      norm_sq_selectedOldDifferenceReal_le_energyIntegral_add_uniformErrors_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct
        hq (n + 1) (Nat.succ_pos n) hε

    dsimp only [A, M, K]

    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hFinite

  have hLimit :
      A ≤ M :=
    ge_of_tendsto hRHS hBound

  simpa only [A, M] using hLimit

/-- Exact selected--old relative-energy inequality under only temporal product
integrability. -/
theorem norm_sq_selectedOldDifferenceReal_le_energyIntegral_of_allTemporalProductIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hProduct :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail)
    (hq : q ∈ Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2
      ≤
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      (∫ r in (0 : ℝ)..q,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2) := by
  let A : ℝ :=
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2

  let M : ℝ :=
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      (∫ r in (0 : ℝ)..q,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2)

  let K : ℝ :=
    24 * h3UnitViscosityZeroRHSBound E * q

  have hInv :
      Tendsto
        (fun n : ℕ =>
          (1 : ℝ) / (((n + 1 : ℕ) : ℝ)))
        atTop
        (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hK :
      Tendsto
        (fun n : ℕ =>
          K * ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))))
        atTop
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _n : ℕ => K)
          atTop
          (𝓝 K) :=
      tendsto_const_nhds

    have hMul :=
      hConst.mul hInv

    simpa only [mul_zero] using hMul

  have hRHS :
      Tendsto
        (fun n : ℕ =>
          M + K * ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))))
        atTop
        (𝓝 M) := by
    have hConst :
        Tendsto
          (fun _n : ℕ => M)
          atTop
          (𝓝 M) :=
      tendsto_const_nhds

    simpa only [add_zero] using
      hConst.add hK

  have hBound :
      ∀ᶠ n : ℕ in atTop,
        A
          ≤
        M + K * ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))) := by
    filter_upwards [] with n

    have hεn :
        0 <
          (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) := by
      positivity

    have hApprox :=
      norm_sq_selectedOldDifferenceReal_le_energyIntegral_add_epsilonError_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct
        hq hεn

    dsimp only [A, M, K]

    calc
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail q‖ ^ 2
          ≤
        6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
            (∫ r in (0 : ℝ)..q,
              ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖ ^ 2)
          +
        24 *
            ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))) *
            h3UnitViscosityZeroRHSBound E * q := hApprox
      _ =
        6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
            (∫ r in (0 : ℝ)..q,
              ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖ ^ 2)
          +
        (24 * h3UnitViscosityZeroRHSBound E * q) *
          ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))) := by
            ring

  have hLimit :
      A ≤ M :=
    ge_of_tendsto hRHS hBound

  simpa only [A, M] using hLimit

end

end Euclidean
end Bridge
end PrimeTensor
