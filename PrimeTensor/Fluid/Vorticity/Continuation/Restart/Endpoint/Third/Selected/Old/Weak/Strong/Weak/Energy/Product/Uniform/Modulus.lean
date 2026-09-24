import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Product.Partition
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Uniform.Modulus

/-!
# Uniform-mesh modulus from temporal product integrability

The selected--old path already satisfies the pressure-free arbitrary-pair
estimate

    ‖D(b) - D(a)‖ ≤ 6 C(E) (b-a)

under the all-test temporal-product family.

This file transports that estimate to the canonical uniform mesh and sums the
two non-integral partition remainders.  The results are identical numerically
to the original pressure-family route:

    ‖ΔD_k‖ ≤ 6 C(E) q/n,

    Σ 2 ε ‖ΔD_k‖ ≤ 12 ε C(E) q,

    Σ ‖ΔD_k‖² ≤ 36 C(E)² q²/n.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyProductUniformModulus
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every consecutive selected--old increment on the uniform mesh obeys the
pressure-free `6 C(E)` step bound. -/
theorem norm_h3PreterminalSelectedOldDifference_uniformPartition_step_le_of_allTemporalProductIntegrable
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
    (n k : ℕ)
    (hn : 0 < n)
    (hk : k < n) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail
          ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
        -
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail
          (((k : ℝ) / (n : ℝ)) * q)‖
      ≤
    (6 * h3UnitViscosityZeroRHSBound E)
      *
    (q / (n : ℝ)) := by
  let x : ℕ → ℝ :=
    fun j : ℕ => ((j : ℝ) / (n : ℝ)) * q

  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hq0 : 0 ≤ q :=
    hq.1

  have hk_le : k ≤ n :=
    Nat.le_of_lt hk

  have hksucc_le : k + 1 ≤ n := by
    omega

  have hxmem :
      ∀ j : ℕ,
        j ≤ n →
          x j ∈ Set.Icc (0 : ℝ) tau := by
    intro j hj

    have hj0 : (0 : ℝ) ≤ (j : ℝ) := by
      positivity

    have hjn : (j : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hj

    have hfrac0 :
        (0 : ℝ) ≤ (j : ℝ) / (n : ℝ) :=
      div_nonneg hj0 (le_of_lt hnR)

    have hfrac1 :
        (j : ℝ) / (n : ℝ) ≤ 1 := by
      exact (div_le_one hnR).2 hjn

    have hx0 : 0 ≤ x j := by
      dsimp only [x]
      exact mul_nonneg hfrac0 hq0

    have hxq : x j ≤ q := by
      dsimp only [x]
      calc
        ((j : ℝ) / (n : ℝ)) * q
            ≤ 1 * q :=
          mul_le_mul_of_nonneg_right hfrac1 hq0
        _ = q := one_mul q

    exact ⟨hx0, hxq.trans hq.2⟩

  have hxmono :
      x k ≤ x (k + 1) := by
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
    norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_sub_le_of_mem_of_allTemporalProductIntegrable
      hNS ht htau hEnd hE hTail htauR hProduct
      (hxmem k hk_le)
      (hxmem (k + 1) hksucc_le)
      hxmono

  have hStep :
      x (k + 1) - x k
        =
      q / (n : ℝ) := by
    dsimp only [x]
    exact
      h3UniformElapsedPartition_step_sub_eq
        (q := q) (n := n) (k := k) hn

  rw [hStep] at h

  simpa only [x] using h

/-- Every point in one uniform mesh cell remains within the same pressure-free
`O(1/n)` radius of the left endpoint. -/
theorem norm_h3PreterminalSelectedOldDifference_uniformPartition_left_sub_le_of_allTemporalProductIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q r : ℝ}
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
    (n k : ℕ)
    (hn : 0 < n)
    (hk : k < n)
    (hr :
      r ∈
        Set.Icc
          (((k : ℝ) / (n : ℝ)) * q)
          ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail
          (((k : ℝ) / (n : ℝ)) * q)
        -
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖
      ≤
    (6 * h3UnitViscosityZeroRHSBound E)
      *
    (q / (n : ℝ)) := by
  let a : ℝ :=
    ((k : ℝ) / (n : ℝ)) * q

  let b : ℝ :=
    (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q

  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hq0 : 0 ≤ q :=
    hq.1

  have hk_le : k ≤ n :=
    Nat.le_of_lt hk

  have hksucc_le : k + 1 ≤ n := by
    omega

  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact
      mul_nonneg
        (div_nonneg (by positivity) (le_of_lt hnR))
        hq0

  have hka : (k : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hk_le

  have hfracA :
      (k : ℝ) / (n : ℝ) ≤ 1 := by
    exact (div_le_one hnR).2 hka

  have haq : a ≤ q := by
    dsimp only [a]
    calc
      ((k : ℝ) / (n : ℝ)) * q
          ≤ 1 * q :=
        mul_le_mul_of_nonneg_right hfracA hq0
      _ = q := one_mul q

  have hbq : b ≤ q := by
    have hkb :
        (((k + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
      exact_mod_cast hksucc_le

    have hfracB :
        (((k + 1 : ℕ) : ℝ)) / (n : ℝ) ≤ 1 := by
      exact (div_le_one hnR).2 hkb

    dsimp only [b]
    calc
      (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q
          ≤ 1 * q :=
        mul_le_mul_of_nonneg_right hfracB hq0
      _ = q := one_mul q

  have hrTau :
      r ∈ Set.Icc (0 : ℝ) tau := by
    exact
      ⟨
        ha0.trans hr.1,
        hr.2.trans (hbq.trans hq.2)
      ⟩

  have haTau :
      a ∈ Set.Icc (0 : ℝ) tau :=
    ⟨ha0, haq.trans hq.2⟩

  have hForward :=
    norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_sub_le_of_mem_of_allTemporalProductIntegrable
      hNS ht htau hEnd hE hTail htauR hProduct
      haTau hrTau hr.1

  have hTime :
      r - a ≤ q / (n : ℝ) := by
    calc
      r - a
          ≤ b - a := by
            linarith [hr.2]
      _ = q / (n : ℝ) := by
            dsimp only [a, b]
            exact
              h3UniformElapsedPartition_step_sub_eq
                (q := q) (n := n) (k := k) hn

  have hCoeff :
      0 ≤ 6 * h3UnitViscosityZeroRHSBound E := by
    exact
      mul_nonneg
        (by norm_num)
        (h3UnitViscosityZeroRHSBound_nonneg hE)

  have hBound :
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail r
          -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail a‖
        ≤
      (6 * h3UnitViscosityZeroRHSBound E)
        *
      (q / (n : ℝ)) := by
    exact
      hForward.trans
        (mul_le_mul_of_nonneg_left hTime hCoeff)

  rw [norm_sub_rev] at hBound

  simpa only [a] using hBound

/-- Sum the endpoint approximation remainders on the pressure-free uniform
mesh. -/
theorem sum_selectedOldDifference_uniformPartition_endpointApproximation_le_of_allTemporalProductIntegrable
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
    (hε : 0 ≤ ε) :
    (∑ k ∈ Finset.range n,
      2 * ε *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail
              ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
          -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail
              (((k : ℝ) / (n : ℝ)) * q)‖)
      ≤
    12 * ε * h3UnitViscosityZeroRHSBound E * q := by
  let C : ℝ :=
    h3UnitViscosityZeroRHSBound E

  let h : ℝ :=
    q / (n : ℝ)

  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hn0 : (n : ℝ) ≠ 0 :=
    ne_of_gt hnR

  have hEach :
      ∀ k ∈ Finset.range n,
        2 * ε *
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail
                  ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
              -
              h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail
                  (((k : ℝ) / (n : ℝ)) * q)‖
          ≤
        2 * ε * ((6 * C) * h) := by
    intro k hk

    have hklt : k < n :=
      Finset.mem_range.mp hk

    have hStep :=
      norm_h3PreterminalSelectedOldDifference_uniformPartition_step_le_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct
        hq n k hn hklt

    have hCoef : 0 ≤ 2 * ε := by
      positivity

    dsimp only [C, h]

    exact
      mul_le_mul_of_nonneg_left
        hStep
        hCoef

  have hSum :
      (∑ k ∈ Finset.range n,
        2 * ε *
          ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail
                ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
            -
            h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail
                (((k : ℝ) / (n : ℝ)) * q)‖)
        ≤
      ∑ _k ∈ Finset.range n,
        2 * ε * ((6 * C) * h) := by
    exact Finset.sum_le_sum hEach

  calc
    (∑ k ∈ Finset.range n,
      2 * ε *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail
              ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
          -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail
              (((k : ℝ) / (n : ℝ)) * q)‖)
        ≤
      ∑ _k ∈ Finset.range n,
        2 * ε * ((6 * C) * h) := hSum
    _ =
      (n : ℝ) * (2 * ε * ((6 * C) * h)) := by
        simp
    _ =
      12 * ε * C * q := by
        dsimp only [h]
        field_simp [hn0]
        ring
    _ =
      12 * ε * h3UnitViscosityZeroRHSBound E * q := by
        rfl

/-- Sum the quadratic polarization remainders on the pressure-free uniform
mesh. -/
theorem sum_sq_selectedOldDifference_uniformPartition_step_le_of_allTemporalProductIntegrable
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
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail
            ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
        -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail
            (((k : ℝ) / (n : ℝ)) * q)‖ ^ 2)
      ≤
    36 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2 / (n : ℝ) := by
  let C : ℝ :=
    h3UnitViscosityZeroRHSBound E

  let h : ℝ :=
    q / (n : ℝ)

  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hn0 : (n : ℝ) ≠ 0 :=
    ne_of_gt hnR

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact h3UnitViscosityZeroRHSBound_nonneg hE

  have hh0 : 0 ≤ h := by
    dsimp only [h]
    exact div_nonneg hq.1 (le_of_lt hnR)

  have hB0 : 0 ≤ (6 * C) * h := by
    positivity

  have hEach :
      ∀ k ∈ Finset.range n,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail
              ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
          -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail
              (((k : ℝ) / (n : ℝ)) * q)‖ ^ 2
          ≤
        ((6 * C) * h) ^ 2 := by
    intro k hk

    have hklt : k < n :=
      Finset.mem_range.mp hk

    have hStep :=
      norm_h3PreterminalSelectedOldDifference_uniformPartition_step_le_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct
        hq n k hn hklt

    have hMul :=
      mul_le_mul
        hStep hStep
        (norm_nonneg _)
        hB0

    simpa only [pow_two] using hMul

  have hSum :
      (∑ k ∈ Finset.range n,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail
              ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
          -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail
              (((k : ℝ) / (n : ℝ)) * q)‖ ^ 2)
        ≤
      ∑ _k ∈ Finset.range n,
        ((6 * C) * h) ^ 2 := by
    exact Finset.sum_le_sum hEach

  calc
    (∑ k ∈ Finset.range n,
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail
            ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
        -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail
            (((k : ℝ) / (n : ℝ)) * q)‖ ^ 2)
        ≤
      ∑ _k ∈ Finset.range n,
        ((6 * C) * h) ^ 2 := hSum
    _ =
      (n : ℝ) * (((6 * C) * h) ^ 2) := by
        simp
    _ =
      36 * C ^ 2 * q ^ 2 / (n : ℝ) := by
        dsimp only [h]
        field_simp [hn0]
        ring
    _ =
      36 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2 / (n : ℝ) := by
        rfl

/-- Combined pressure-free non-integral uniform-mesh remainder. -/
theorem sum_selectedOldDifference_uniformPartition_endpointAndQuadratic_le_of_allTemporalProductIntegrable
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
    (hε : 0 ≤ ε) :
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
            (((k : ℝ) / (n : ℝ)) * q)‖ ^ 2))
      ≤
    12 * ε * h3UnitViscosityZeroRHSBound E * q
      +
    36 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2 / (n : ℝ) := by
  rw [Finset.sum_add_distrib]

  exact
    add_le_add
      (sum_selectedOldDifference_uniformPartition_endpointApproximation_le_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct
        hq n hn hε)
      (sum_sq_selectedOldDifference_uniformPartition_step_le_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct
        hq n hn)

end

end Euclidean
end Bridge
end PrimeTensor
