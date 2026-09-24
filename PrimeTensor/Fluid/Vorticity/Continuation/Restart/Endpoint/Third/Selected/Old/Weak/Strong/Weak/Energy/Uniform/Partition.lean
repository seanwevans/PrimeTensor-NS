import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Partition

/-!
# Uniform-partition weak-energy estimate

The preceding partition theorem accepts an arbitrary monotone node family.  For
the mesh-limit argument we now specialize it to the canonical uniform partition

    x k = (k / n) q,    0 <= k <= n,

of `[0,q]`.

This is intentionally only the geometric specialization.  No temporal error is
discarded here.  In particular, the quadratic increment sum remains visible
until a genuine modulus strong enough to control it has been proved for the
selected--old difference path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyUniformPartition
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The anchored finite-partition estimate on the canonical uniform `n`-mesh
of `[0,q]`. -/
theorem norm_sq_selectedOldDifferenceReal_le_uniformPartitionApproximateEnergyIncrement
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
    norm_sq_selectedOldDifferenceReal_le_partitionApproximateEnergyIncrement
      hNS ht htau hEnd hE hTail htauR hPressure
      n x hx0 hxn hxmem hxmono hε

  simpa only [x] using h

end

end Euclidean
end Bridge
end PrimeTensor
