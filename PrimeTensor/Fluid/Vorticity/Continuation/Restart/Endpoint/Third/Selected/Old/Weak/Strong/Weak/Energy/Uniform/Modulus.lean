import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Uniform.Partition
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Velocity.Lipschitz

/-!
# Uniform-mesh modulus for the selected--old weak energy path

The selected--old physical difference now has the strong arbitrary-pair bound

    ‖D(b) - D(a)‖ ≤ 6 C(E) (b-a)

for ordered elapsed times in `[0,tau]`.

This file transports that estimate to the ambient-real extension used by the
weak-energy partition argument and specializes it to the canonical uniform
mesh

    x_k = (k / n) q.

Consequently every mesh endpoint increment and every within-cell oscillation is
bounded by

    6 C(E) q / n.

These are exactly the pointwise estimates needed to collapse the remaining
partition error sums.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyUniformModulus
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Ambient-real version of the strong selected--old temporal modulus. -/
theorem norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_sub_le_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau a b : ℝ}
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
    (ha : a ∈ Set.Icc (0 : ℝ) tau)
    (hb : b ∈ Set.Icc (0 : ℝ) tau)
    (hab : a ≤ b) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail b
        -
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail a‖
      ≤
    (6 * h3UnitViscosityZeroRHSBound E) * (b - a) := by
  rw [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail hb,
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail ha
  ]

  exact
    norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_sub_le
      hNS ht htau hEnd hE hTail htauR hPressure
      ⟨a, ha⟩ ⟨b, hb⟩ hab

/-- One uniform mesh step has exact width `q / n`. -/
theorem h3UniformElapsedPartition_step_sub_eq
    {q : ℝ}
    {n k : ℕ}
    (hn : 0 < n) :
    ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q)
      -
    (((k : ℝ) / (n : ℝ)) * q)
      =
    q / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hn0 : (n : ℝ) ≠ 0 :=
    ne_of_gt hnR

  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [hn0]
  ring

/-- Every consecutive selected--old difference increment on the uniform mesh
has the expected `O(1/n)` norm bound. -/
theorem norm_h3PreterminalSelectedOldDifference_uniformPartition_step_le
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
    norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_sub_le_of_mem
      hNS ht htau hEnd hE hTail htauR hPressure
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

/-- Every point inside one uniform mesh cell remains within the same `O(1/n)`
selected--old difference radius of the left endpoint. -/
theorem norm_h3PreterminalSelectedOldDifference_uniformPartition_left_sub_le
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
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
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
    have hkb : (((k + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
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

  have hOrdered :
      a ≤ r :=
    hr.1

  have hForward :=
    norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_sub_le_of_mem
      hNS ht htau hEnd hE hTail htauR hPressure
      haTau hrTau hOrdered

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

end

end Euclidean
end Bridge
end PrimeTensor
