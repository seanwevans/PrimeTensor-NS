import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Uniform.Modulus

/-!
# Summed uniform-mesh weak-energy remainders

The uniform-mesh modulus gives, on every cell,

    ‖D(x_{k+1}) - D(x_k)‖ ≤ 6 C(E) q / n.

This file performs the first finite-sum collapse in the weak-energy argument.

The endpoint approximation remainder satisfies

    Σ 2 ε ‖ΔD_k‖ ≤ 12 ε C(E) q,

while the quadratic polarization remainder satisfies

    Σ ‖ΔD_k‖² ≤ 36 C(E)² q² / n.

Thus the non-integral mesh error is explicitly `O(ε) + O(1/n)`.
No limiting argument is taken yet.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyUniformRemainder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Sum the endpoint weak-test approximation errors over the uniform mesh. -/
theorem sum_selectedOldDifference_uniformPartition_endpointApproximation_le
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
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
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
      norm_h3PreterminalSelectedOldDifference_uniformPartition_step_le
        hNS ht htau hEnd hE hTail htauR hPressure
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
    exact
      Finset.sum_le_sum hEach

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

/-- Sum the genuine quadratic polarization remainder over the uniform mesh.
The bound is explicitly `O(1/n)`. -/
theorem sum_sq_selectedOldDifference_uniformPartition_step_le
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
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
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
    exact
      div_nonneg hq.1 (le_of_lt hnR)

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
      norm_h3PreterminalSelectedOldDifference_uniformPartition_step_le
        hNS ht htau hEnd hE hTail htauR hPressure
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
    exact
      Finset.sum_le_sum hEach

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

/-- Combined non-integral remainder appearing in the uniform-partition
weak-energy inequality. -/
theorem sum_selectedOldDifference_uniformPartition_endpointAndQuadratic_le
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
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
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
      (sum_selectedOldDifference_uniformPartition_endpointApproximation_le
        hNS ht htau hEnd hE hTail htauR hPressure
        hq n hn hε)
      (sum_sq_selectedOldDifference_uniformPartition_step_le
        hNS ht htau hEnd hE hTail htauR hPressure
        hq n hn)

end

end Euclidean
end Bridge
end PrimeTensor
