import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Selected.Enstrophy.Rate

/-!
# Indexed enstrophy and the physical endpoint clock

The selected pointwise enstrophy theorem gives divergence after
division by the original native index. That rate alone does not
control the enstrophy multiplied by the physical time remaining to
the endpoint. An explicit scalar model below satisfies the same
near-terminal sampling window, has divergent indexed enstrophy, and
has a vanishing physical-clock product. It is an abstract comparison,
not a Navier-Stokes solution or a counterexample to continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A positive native-index scale with a one-step cushion. -/
def h3NativeSampleClockIndex (n : ℕ) : ℝ := (n : ℝ) + 2

/-- A physical endpoint gap much shorter than the native window. -/
def h3NativeSampleClockGap (n : ℕ) : ℝ :=
  1 / h3NativeSampleClockIndex n ^ 3

/-- Abstract pointwise enstrophy growing quadratically in that index. -/
def h3NativeSampleEnstrophy (n : ℕ) : ℝ :=
  h3NativeSampleClockIndex n ^ 2

/-- The native near-terminal window and divergent indexed enstrophy
do not imply growth in the physical endpoint clock. -/
theorem native_indexedEnstrophy_does_not_force_physicalClockProduct
    (T : ℝ) :
    (∀ n : ℕ,
      T - h3NativeSampleClockGap n ∈
        Set.Ioo (T - 1 / ((n : ℝ) + 1)) T) ∧
    Tendsto
      (fun n : ℕ =>
        h3NativeSampleEnstrophy n / h3NativeSampleClockIndex n)
      atTop atTop ∧
    Tendsto
      (fun n : ℕ =>
        h3NativeSampleClockGap n * h3NativeSampleEnstrophy n)
      atTop (𝓝 (0 : ℝ)) := by
  have hIndexPos : ∀ n : ℕ, 0 < h3NativeSampleClockIndex n := by
    intro n
    unfold h3NativeSampleClockIndex
    positivity
  have hIndexOne : ∀ n : ℕ, 1 ≤ h3NativeSampleClockIndex n := by
    intro n
    unfold h3NativeSampleClockIndex
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hGapPos : ∀ n : ℕ, 0 < h3NativeSampleClockGap n := by
    intro n
    unfold h3NativeSampleClockGap
    exact div_pos (by norm_num) (pow_pos (hIndexPos n) 3)
  have hGapSmall : ∀ n : ℕ,
      h3NativeSampleClockGap n < 1 / ((n : ℝ) + 1) := by
    intro n
    let D : ℝ := h3NativeSampleClockIndex n
    have hD : 0 < D := hIndexPos n
    have hDOne : 1 ≤ D := hIndexOne n
    have hNearDen : (n : ℝ) + 1 < D := by
      dsimp [D, h3NativeSampleClockIndex]
      linarith
    have hDSq : 1 ≤ D ^ 2 := by
      nlinarith [sq_nonneg (D - 1)]
    have hDCube : D ≤ D ^ 3 := by
      have hMul : 0 ≤ D * (D ^ 2 - 1) :=
        mul_nonneg (le_of_lt hD) (by linarith)
      nlinarith [hMul]
    have hClock : (n : ℝ) + 1 < D ^ 3 :=
      lt_of_lt_of_le hNearDen hDCube
    have hNearPos : 0 < (n : ℝ) + 1 := by positivity
    have hCubePos : 0 < D ^ 3 := pow_pos hD 3
    change 1 / D ^ 3 < 1 / ((n : ℝ) + 1)
    exact (div_lt_div_iff₀ hCubePos hNearPos).2 (by simpa using hClock)
  have hIndexTop : Tendsto h3NativeSampleClockIndex atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro C
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt C
    filter_upwards [eventually_ge_atTop N] with n hn
    have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [h3NativeSampleClockIndex]
    linarith
  have hIndexedEq :
      (fun n : ℕ =>
        h3NativeSampleEnstrophy n / h3NativeSampleClockIndex n) =
        h3NativeSampleClockIndex := by
    funext n
    unfold h3NativeSampleEnstrophy
    have hNe : h3NativeSampleClockIndex n ≠ 0 :=
      ne_of_gt (hIndexPos n)
    field_simp [hNe] <;> ring
  have hClockEq :
      (fun n : ℕ =>
        h3NativeSampleClockGap n * h3NativeSampleEnstrophy n) =
        (fun n : ℕ => (h3NativeSampleClockIndex n)⁻¹) := by
    funext n
    unfold h3NativeSampleClockGap h3NativeSampleEnstrophy
    have hNe : h3NativeSampleClockIndex n ≠ 0 :=
      ne_of_gt (hIndexPos n)
    field_simp [hNe] <;> ring
  constructor
  · intro n
    exact ⟨by linarith [hGapSmall n], by linarith [hGapPos n]⟩
  constructor
  · rw [hIndexedEq]
    exact hIndexTop
  · rw [hClockEq]
    exact tendsto_inv_atTop_zero.comp hIndexTop

end

end Euclidean
end Bridge
end PrimeTensor
