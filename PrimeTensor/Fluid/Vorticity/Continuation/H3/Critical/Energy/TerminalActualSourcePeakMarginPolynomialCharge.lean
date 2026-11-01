import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourcePeakCalibratedWidthCompression
import Mathlib.Tactic

/-!
# Eliminate the quartic radius from the physical source-peak charge

The calibrated source-peak width is
  δ = min(w, (max(1,σ) + 1 + A²B/P²)⁻⁴).
A physical dissipation charge J ≥ Mδ therefore forces either compression of
w or a denominator-free *fourth-degree* constraint on the true PDE budget B
and actual Fourier-source excess P:

  M P⁸ ≤ J ((max(1,σ)+1)P² + A²B)⁴.

We retain the P=0 case (where the polynomial constraint is trivial), so the
result can be applied to existing cofinal witness interfaces which do not
export positivity of P, even though their actual source witnesses are strict.
No terminal-uniform PDE source, H³ energy, or dissipation bound is introduced.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Clearing the exact calibrated radius denominator turns quartic frequency
into a polynomial in the actual source margin P and PDE cost A²B. -/
theorem h3Critical_calibratedRadius_sourceMargin_fourthPowerIdentity
    (σ P A B : ℝ) (hP : P ≠ 0) :
    (h3CriticalSourcePeakCalibratedRadius σ P A B) ^ 4 * P ^ 8 =
      ((max 1 σ + 1) * P ^ 2 + A ^ 2 * B) ^ 4 := by
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero 2 hP
  have hProduct :
      h3CriticalSourcePeakCalibratedRadius σ P A B * P ^ 2 =
        (max 1 σ + 1) * P ^ 2 + A ^ 2 * B := by
    dsimp only [h3CriticalSourcePeakCalibratedRadius]
    field_simp [hP2]
    <;> ring
  calc
    (h3CriticalSourcePeakCalibratedRadius σ P A B) ^ 4 * P ^ 8 =
        (h3CriticalSourcePeakCalibratedRadius σ P A B * P ^ 2) ^ 4 := by
          ring
    _ = ((max 1 σ + 1) * P ^ 2 + A ^ 2 * B) ^ 4 := by
          rw [hProduct]

/-- An individual finite dissipation charge forces a short original window,
or a denominator-free inequality linking the actual source excess to PDE
source/spectral/viscous costs. This is valid even for P=0. -/
theorem h3Critical_calibratedFiniteCharge_forces_window_or_marginPolynomial
    (σ P A B w M J : ℝ)
    (hB : 0 ≤ B) (hM : 0 < M) (hJ : 0 < J)
    (hCharge :
      M * min w (1 / (h3CriticalSourcePeakCalibratedRadius σ P A B) ^ 4) ≤ J) :
    w ≤ J / M ∨
      M * P ^ 8 ≤
        J * ((max 1 σ + 1) * P ^ 2 + A ^ 2 * B) ^ 4 := by
  let R : ℝ := h3CriticalSourcePeakCalibratedRadius σ P A B
  have hBcost : 0 ≤ A ^ 2 * B := mul_nonneg (sq_nonneg _) hB
  have hDiv : 0 ≤ A ^ 2 * B / P ^ 2 :=
    div_nonneg hBcost (sq_nonneg P)
  have hR : 0 < R := by
    dsimp only [R, h3CriticalSourcePeakCalibratedRadius]
    have hQ : (1 : ℝ) ≤ max 1 σ := le_max_left _ _
    linarith only [hQ, hDiv]
  have hAlt := h3Critical_calibratedQuarticWidth_finiteCharge_forces_compression
    w R M J hR hM hJ hCharge
  rcases hAlt with hWindow | hRadius
  · exact Or.inl hWindow
  · right
    by_cases hP : P = 0
    · subst P
      have hNonneg :
          (0 : ℝ) ≤ J * ((max 1 σ + 1) * (0 : ℝ) ^ 2 + A ^ 2 * B) ^ 4 := by
        positivity
      simpa using hNonneg
    · have hIdentity :=
        h3Critical_calibratedRadius_sourceMargin_fourthPowerIdentity
          σ P A B hP
      have hBound : M ≤ R ^ 4 * J :=
        (div_le_iff₀ hJ).mp hRadius
      have hPow : 0 ≤ P ^ 8 := by positivity
      have hScale := mul_le_mul_of_nonneg_right hBound hPow
      calc
        M * P ^ 8 ≤ (R ^ 4 * J) * P ^ 8 := hScale
        _ = J * ((max 1 σ + 1) * P ^ 2 + A ^ 2 * B) ^ 4 := by
          rw [← hIdentity]
          ring

/-- If the original physical window is not compressed enough to pay the
charge, the actual source excess must satisfy the polynomial PDE constraint. -/
theorem h3Critical_noncompressedCalibratedCharge_forces_marginPolynomial
    (σ P A B w M J : ℝ)
    (hB : 0 ≤ B) (hM : 0 < M) (hJ : 0 < J)
    (hNoncompressed : J / M < w)
    (hCharge :
      M * min w (1 / (h3CriticalSourcePeakCalibratedRadius σ P A B) ^ 4) ≤ J) :
    M * P ^ 8 ≤
      J * ((max 1 σ + 1) * P ^ 2 + A ^ 2 * B) ^ 4 := by
  rcases h3Critical_calibratedFiniteCharge_forces_window_or_marginPolynomial
      σ P A B w M J hB hM hJ hCharge with hShort | hPoly
  · exact False.elim ((not_le_of_gt hNoncompressed) hShort)
  · exact hPoly

/-- The denominator-free obstruction for a genuine physical H³
viscous-dissipation integral, with no separate charge assumption. -/
theorem h3Critical_physicalDissipationBudget_forces_marginPolynomial_or_width
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t w δ σ P A B M J : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hM : 0 < M) (hJ : 0 < J)
    (hCal : δ = min w (1 / (h3CriticalSourcePeakCalibratedRadius σ P A B) ^ 4))
    (hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      M ≤ velocityH3DissipationAt u s)
    (hBudget :
      (∫⁻ s in Set.Ioc t (t + δ),
        ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
          ENNReal.ofReal J) :
    w ≤ J / M ∨
      M * P ^ 8 ≤
        J * ((max 1 σ + 1) * P ^ 2 + A ^ 2 * B) ^ 4 := by
  have hWidth : δ ≤ J / M :=
    h3Critical_extendedWindowBudget_width_le
      (velocityH3DissipationAt u) t δ M J hδ hM hJ.le
      hFloor hBudget
  have hCharge :
      M * min w (1 / (h3CriticalSourcePeakCalibratedRadius σ P A B) ^ 4) ≤ J := by
    have hMul := (le_div_iff₀ hM).1 hWidth
    rw [hCal] at hMul
    simpa only [mul_comm] using hMul
  exact h3Critical_calibratedFiniteCharge_forces_window_or_marginPolynomial
    σ P A B w M J hB hM hJ hCharge

/-- The actual cofinal time-window arrays can be fed directly into a
quantitative budget gate; no uniform bound across k is necessary. -/
theorem h3Critical_calibratedFamily_physicalCharges_force_marginPolynomial
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t w δ σ P A B M J : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k)
    (hδ : ∀ k, 0 ≤ δ k)
    (hM : ∀ k, 0 < M k)
    (hJ : ∀ k, 0 < J k)
    (hCal : ∀ k, δ k =
      min (w k) (1 / (h3CriticalSourcePeakCalibratedRadius
        (σ k) (P k) (A k) (B k)) ^ 4))
    (hFloor : ∀ k s, s ∈ Set.Icc (t k) (t k + δ k) →
      M k ≤ velocityH3DissipationAt u s)
    (hBudget : ∀ k,
      (∫⁻ s in Set.Ioc (t k) (t k + δ k),
        ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
          ENNReal.ofReal (J k)) :
    ∀ k, w k ≤ J k / M k ∨
      M k * (P k) ^ 8 ≤
        J k * ((max 1 (σ k) + 1) * (P k) ^ 2 + (A k) ^ 2 * (B k)) ^ 4 := by
  intro k
  exact h3Critical_physicalDissipationBudget_forces_marginPolynomial_or_width
    u (t k) (w k) (δ k) (σ k) (P k) (A k) (B k) (M k) (J k)
    (hB k) (hδ k) (hM k) (hJ k) (hCal k)
    (hFloor k) (hBudget k)

end
end PrimeTensor.Bridge.Euclidean
