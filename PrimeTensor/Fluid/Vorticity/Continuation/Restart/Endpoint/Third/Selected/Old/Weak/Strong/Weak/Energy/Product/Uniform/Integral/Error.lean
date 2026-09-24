import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Product.Uniform.Modulus

/-!
# Uniform-mesh integral error from temporal product integrability

The remaining mesh-dependent term inside the weak-energy integral is

    2 * Σ_k ∫_{x_k}^{x_{k+1}}
      (ε + ‖D(x_k) - D(r)‖) * 6 C(E) dr.

The product-integrability temporal modulus gives on each uniform cell

    ‖D(x_k) - D(r)‖ ≤ 6 C(E) q / n.

Hence the same numerical estimate as in the original pressure-family route
holds without any pressure hypothesis:

    12 ε C(E) q + 72 C(E)^2 q^2 / n.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyProductUniformIntegralError
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One uniform cell's integral approximation error under only temporal product
integrability. -/
theorem selectedOldDifference_uniformPartition_cellIntegralError_le_of_allTemporalProductIntegrable
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
    (n k : ℕ)
    (hn : 0 < n)
    (hk : k < n)
    (hε : 0 ≤ ε) :
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
          (6 * h3UnitViscosityZeroRHSBound E))
      ≤
    2 *
      ((ε +
          (6 * h3UnitViscosityZeroRHSBound E) *
            (q / (n : ℝ)))
        *
        (6 * h3UnitViscosityZeroRHSBound E))
      *
      (q / (n : ℝ)) := by
  let a : ℝ :=
    ((k : ℝ) / (n : ℝ)) * q

  let b : ℝ :=
    (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q

  let C : ℝ :=
    h3UnitViscosityZeroRHSBound E

  let h : ℝ :=
    q / (n : ℝ)

  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
      hNS ht hEnd hE hTail

  let F : ℝ → ℝ :=
    fun r : ℝ =>
      (ε + ‖D a - D r‖) * (6 * C)

  let K : ℝ :=
    (ε + (6 * C) * h) * (6 * C)

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

  have hkb :
      (((k + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hksucc_le

  have hfracB :
      (((k + 1 : ℕ) : ℝ)) / (n : ℝ) ≤ 1 := by
    exact (div_le_one hnR).2 hkb

  have hbq : b ≤ q := by
    dsimp only [b]
    calc
      (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * q
          ≤ 1 * q :=
        mul_le_mul_of_nonneg_right hfracB hq0
      _ = q := one_mul q

  have hab : a ≤ b := by
    have hkSucc :
        (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_succ k)

    have hDiv :
        (k : ℝ) / (n : ℝ)
          ≤
        ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right hnR).2 hkSucc

    dsimp only [a, b]
    exact mul_le_mul_of_nonneg_right hDiv hq0

  have hSub :
      Set.Icc a b
        ⊆
      Set.Icc (0 : ℝ) tau := by
    intro r hr
    exact
      ⟨
        ha0.trans hr.1,
        hr.2.trans (hbq.trans hq.2)
      ⟩

  have hDCont :
      ContinuousOn D (Set.Icc a b) := by
    dsimp only [D]
    exact
      (continuousOn_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct).mono hSub

  have hDaCont :
      ContinuousOn
        (fun _r : ℝ => D a)
        (Set.Icc a b) :=
    continuousOn_const

  have hNormCont :
      ContinuousOn
        (fun r : ℝ => ‖D a - D r‖)
        (Set.Icc a b) :=
    continuous_norm.comp_continuousOn
      (hDaCont.sub hDCont)

  have hFCont :
      ContinuousOn F (Set.Icc a b) := by
    dsimp only [F]
    exact
      (continuousOn_const.add hNormCont).mul
        continuousOn_const

  have hFInt :
      IntervalIntegrable F volume a b :=
    hFCont.intervalIntegrable_of_Icc hab

  have hKInt :
      IntervalIntegrable
        (fun _r : ℝ => K)
        volume
        a b :=
    continuousOn_const.intervalIntegrable_of_Icc hab

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact h3UnitViscosityZeroRHSBound_nonneg hE

  have hSixC0 : 0 ≤ 6 * C := by
    positivity

  have hPointwise :
      ∀ r ∈ Set.Icc a b,
        F r ≤ K := by
    intro r hr

    have hNorm :=
      norm_h3PreterminalSelectedOldDifference_uniformPartition_left_sub_le_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct
        hq n k hn hk
        (by
          simpa only [a, b] using hr)

    have hAdd :
        ε + ‖D a - D r‖
          ≤
        ε + (6 * C) * h := by
      dsimp only [D, a, C, h] at hNorm ⊢
      exact add_le_add (le_refl ε) hNorm

    dsimp only [F, K]
    exact
      mul_le_mul_of_nonneg_right
        hAdd
        hSixC0

  have hIntegral :
      (∫ r in a..b, F r)
        ≤
      ∫ _r in a..b, K := by
    exact
      intervalIntegral.integral_mono_on
        hab hFInt hKInt hPointwise

  have hStep :
      b - a = h := by
    dsimp only [a, b, h]
    exact
      h3UniformElapsedPartition_step_sub_eq
        (q := q) (n := n) (k := k) hn

  have hConst :
      (∫ _r in a..b, K)
        =
      (b - a) * K := by
    simp

  rw [hConst, hStep] at hIntegral

  have hTwo :=
    mul_le_mul_of_nonneg_left
      hIntegral
      (by norm_num : (0 : ℝ) ≤ 2)

  dsimp only [F, K, D, C, h, a, b] at hTwo ⊢

  nlinarith

/-- Summing the pressure-free within-cell approximation integrals yields the
explicit `O(ε) + O(1/n)` bound. -/
theorem sum_selectedOldDifference_uniformPartition_cellIntegralError_le_of_allTemporalProductIntegrable
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
      ≤
    12 * ε * h3UnitViscosityZeroRHSBound E * q
      +
    72 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2 / (n : ℝ) := by
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
              (6 * C))
          ≤
        2 * ((ε + (6 * C) * h) * (6 * C)) * h := by
    intro k hk

    have hklt : k < n :=
      Finset.mem_range.mp hk

    dsimp only [C, h]

    exact
      selectedOldDifference_uniformPartition_cellIntegralError_le_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct
        hq n k hn hklt hε

  have hSum :
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
            (6 * C)))
        ≤
      ∑ _k ∈ Finset.range n,
        2 * ((ε + (6 * C) * h) * (6 * C)) * h := by
    exact
      Finset.sum_le_sum hEach

  calc
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
        ≤
      ∑ _k ∈ Finset.range n,
        2 * ((ε + (6 * C) * h) * (6 * C)) * h := by
          simpa only [C] using hSum
    _ =
      (n : ℝ) *
        (2 * ((ε + (6 * C) * h) * (6 * C)) * h) := by
          simp
    _ =
      12 * ε * C * q
        +
      72 * C ^ 2 * q ^ 2 / (n : ℝ) := by
          dsimp only [h]
          field_simp [hn0]
          ring
    _ =
      12 * ε * h3UnitViscosityZeroRHSBound E * q
        +
      72 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2 / (n : ℝ) := by
          rfl

end

end Euclidean
end Bridge
end PrimeTensor
