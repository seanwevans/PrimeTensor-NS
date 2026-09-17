import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyProductIncrement
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldL2DifferenceInitial

/-!
# Finite and uniform partition estimates from temporal product integrability

The local squared-energy increment is now available without pressure.  This file
performs the same finite telescoping argument as the original pressure-family
route, but with the temporal-product family as the sole old-branch hypothesis.

It then specializes the result to the canonical uniform mesh

    x k = (k / n) q.

No mesh error is discarded here; the output has exactly the same numerical
shape as the existing pressure-based uniform-partition estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyProductPartition
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Sum the product-integrability local squared-energy estimate over an
arbitrary finite monotone partition in `[0,tau]`. -/
theorem norm_sq_selectedOldDifferenceReal_sub_le_partitionApproximateEnergyIncrement_of_allTemporalProductIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
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
    (n : ℕ)
    (x : ℕ → ℝ)
    (hxmem :
      ∀ k : ℕ,
        k ≤ n →
          x k ∈ Set.Icc (0 : ℝ) tau)
    (hxmono :
      ∀ k : ℕ,
        k < n →
          x k ≤ x (k + 1))
    {ε : ℝ}
    (hε : 0 < ε) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail (x n)‖ ^ 2
      -
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail (x 0)‖ ^ 2
      ≤
    ∑ k ∈ Finset.range n,
      (2 *
        (∫ r in x k..x (k + 1),
          3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
              ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖ ^ 2
            +
          (ε +
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail (x k)
              -
              h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail r‖)
            *
          (6 * h3UnitViscosityZeroRHSBound E))
        +
      2 * ε *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail (x (k + 1))
          -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail (x k)‖
        +
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail (x (k + 1))
          -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail (x k)‖ ^ 2) := by
  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
      hNS ht hEnd hE hTail

  let R : ℕ → ℝ :=
    fun k : ℕ =>
      2 *
        (∫ r in x k..x (k + 1),
          3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
              ‖D r‖ ^ 2
            +
          (ε + ‖D (x k) - D r‖) *
            (6 * h3UnitViscosityZeroRHSBound E))
        +
      2 * ε * ‖D (x (k + 1)) - D (x k)‖
        +
      ‖D (x (k + 1)) - D (x k)‖ ^ 2

  have hCell :
      ∀ k ∈ Finset.range n,
        ‖D (x (k + 1))‖ ^ 2 - ‖D (x k)‖ ^ 2
          ≤ R k := by
    intro k hk

    have hklt : k < n :=
      Finset.mem_range.mp hk

    have hk_le : k ≤ n :=
      Nat.le_of_lt hklt

    have hksucc_le : k + 1 ≤ n := by
      omega

    dsimp only [D, R]

    exact
      norm_sq_selectedOldDifferenceReal_sub_le_approximateEnergyIncrement_of_mem_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct
        (hxmem k hk_le)
        (hxmem (k + 1) hksucc_le)
        (hxmono k hklt)
        hε

  have hSum :
      (∑ k ∈ Finset.range n,
        (‖D (x (k + 1))‖ ^ 2 - ‖D (x k)‖ ^ 2))
        ≤
      ∑ k ∈ Finset.range n, R k := by
    exact Finset.sum_le_sum hCell

  rw [
    Finset.sum_range_sub
      (fun k : ℕ => ‖D (x k)‖ ^ 2)
      n
  ] at hSum

  simpa only [D, R] using hSum

/-- The product-integrability partition estimate anchored at elapsed zero. -/
theorem norm_sq_selectedOldDifferenceReal_le_partitionApproximateEnergyIncrement_of_allTemporalProductIntegrable
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
    (n : ℕ)
    (x : ℕ → ℝ)
    (hx0 : x 0 = 0)
    (hxn : x n = q)
    (hxmem :
      ∀ k : ℕ,
        k ≤ n →
          x k ∈ Set.Icc (0 : ℝ) tau)
    (hxmono :
      ∀ k : ℕ,
        k < n →
          x k ≤ x (k + 1))
    {ε : ℝ}
    (hε : 0 < ε) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2
      ≤
    ∑ k ∈ Finset.range n,
      (2 *
        (∫ r in x k..x (k + 1),
          3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
              ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖ ^ 2
            +
          (ε +
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail (x k)
              -
              h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail r‖)
            *
          (6 * h3UnitViscosityZeroRHSBound E))
        +
      2 * ε *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail (x (k + 1))
          -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail (x k)‖
        +
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail (x (k + 1))
          -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail (x k)‖ ^ 2) := by
  have hPartition :=
    norm_sq_selectedOldDifferenceReal_sub_le_partitionApproximateEnergyIncrement_of_allTemporalProductIntegrable
      hNS ht htau hEnd hE hTail htauR hProduct
      n x hxmem hxmono hε

  have hZeroMem :
      (0 : ℝ) ∈ Set.Icc (0 : ℝ) tau :=
    ⟨le_rfl, htau.le⟩

  have hDZero :
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail 0
        =
      0 := by
    rw [
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
        hNS ht hEnd hE hTail hZeroMem
    ]

    exact
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_zero
        (one_pos : (0 : ℝ) < 1)
        hNS ht htau hEnd hE hTail

  rw [hx0, hxn] at hPartition

  have hInitialEnergy :
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail 0‖ ^ 2
        =
      0 := by
    rw [hDZero]
    norm_num

  rw [hInitialEnergy, sub_zero] at hPartition

  exact hPartition

/-- The product-integrability partition estimate specialized to the canonical
uniform `n`-mesh of `[0,q]`. -/
theorem norm_sq_selectedOldDifferenceReal_le_uniformPartitionApproximateEnergyIncrement_of_allTemporalProductIntegrable
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
    (hn : 0 < n)
    {ε : ℝ}
    (hε : 0 < ε) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2
      ≤
    ∑ k ∈ Finset.range n,
      (2 *
        (∫ r in
            ((k : ℝ) / (n : ℝ)) * q..
            (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q,
          3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
              ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖ ^ 2
            +
          (ε +
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail
                  (((k : ℝ) / (n : ℝ)) * q)
              -
              h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail r‖) *
          (6 * h3UnitViscosityZeroRHSBound E))
        +
      2 * ε *
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
            (((k : ℝ) / (n : ℝ)) * q)‖ ^ 2) := by
  let x : ℕ → ℝ :=
    fun k : ℕ => ((k : ℝ) / (n : ℝ)) * q

  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hq0 : 0 ≤ q :=
    hq.1

  have hqtau : q ≤ tau :=
    hq.2

  have hx0 : x 0 = 0 := by
    simp [x]

  have hxn : x n = q := by
    simp [x, ne_of_gt hnR]

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

    have hx0' : 0 ≤ x k := by
      dsimp only [x]
      exact mul_nonneg hfrac0 hq0

    have hxq : x k ≤ q := by
      dsimp only [x]
      calc
        ((k : ℝ) / (n : ℝ)) * q
            ≤ 1 * q :=
          mul_le_mul_of_nonneg_right hfrac1 hq0
        _ = q := one_mul q

    exact ⟨hx0', hxq.trans hqtau⟩

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

  have h :=
    norm_sq_selectedOldDifferenceReal_le_partitionApproximateEnergyIncrement_of_allTemporalProductIntegrable
      hNS ht htau hEnd hE hTail htauR hProduct
      n x hx0 hxn hxmem hxmono hε

  simpa only [x] using h

end

end Euclidean
end Bridge
end PrimeTensor
