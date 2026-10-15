import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3CriticalEnergyExponent

/-!
# Exact critical-half amplitude-ray coefficient threshold

The preceding theorem proves that theta < 1/2 is impossible for a fixed
energy-weighted dissipation coefficient on all amplitudes of a real
divergence-free Schwartz witness. This module examines the exact endpoint
theta = 1/2 instead.

A real-variable theorem characterizes when a fixed coefficient works along
*every* positive amplitude on one ray. Its criterion is a squared inequality
among the three base values M, E and B, with E and B nonnegative.

The result is applied to the actual 243-slot first monomial and the absolute
values of the full quadratic H3 energy and top dissipation. The positive
Schwartz witness gives a concrete necessary coefficient threshold.

This is an amplitude-ray calculation, not a global interpolation inequality
and not a continuation theorem for a PDE trajectory.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterCriticalHalf (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- **Exact endpoint threshold on one amplitude ray.**  For `M > 0`,
`E >= 0`, `B >= 0`, the critical-half bound at every positive amplitude is
equivalent to `M² <= B² E`.  This treats `E = 0` and `B = 0` without divisions
by either quantity. -/
theorem criticalHalfEnergyRayBound_iff
    (M E B : ℝ) (hM : 0 < M) (hE : 0 ≤ E) (hB : 0 ≤ B) :
    (∀ a : ℝ, 0 < a →
      a ^ 3 * M ≤ B * Real.sqrt (1 + a ^ 2 * E) * a ^ 2) ↔
      M ^ 2 ≤ B ^ 2 * E := by
  constructor
  · intro h
    by_contra hn
    have hdelta : 0 < M ^ 2 - B ^ 2 * E :=
      sub_pos.mpr (lt_of_not_ge hn)
    let a : ℝ := B ^ 2 / (M ^ 2 - B ^ 2 * E) + 1
    have ha1 : 1 ≤ a := by
      dsimp [a]
      have hNonneg : 0 ≤ B ^ 2 / (M ^ 2 - B ^ 2 * E) :=
        div_nonneg (sq_nonneg _) hdelta.le
      linarith
    have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
    have hFormula :
        a * (M ^ 2 - B ^ 2 * E) =
          B ^ 2 + (M ^ 2 - B ^ 2 * E) := by
      dsimp [a]
      rw [add_mul, div_mul_cancel₀ _ hdelta.ne', one_mul]
    have hA2 : a ≤ a ^ 2 := by
      nlinarith [sq_nonneg (a - 1)]
    have hLarge : B ^ 2 < a ^ 2 * (M ^ 2 - B ^ 2 * E) := by
      have hFirst : B ^ 2 < a * (M ^ 2 - B ^ 2 * E) := by
        rw [hFormula]
        linarith
      exact lt_of_lt_of_le hFirst (mul_le_mul_of_nonneg_right hA2 hdelta.le)
    let s : ℝ := Real.sqrt (1 + a ^ 2 * E)
    have hs : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = 1 + a ^ 2 * E :=
      Real.sq_sqrt (by positivity)
    have hMain := h a ha
    change a ^ 3 * M ≤ B * s * a ^ 2 at hMain
    have hReduced : a * M ≤ B * s := by
      apply (mul_le_mul_iff_of_pos_left (pow_pos ha 2)).mp
      calc
        a ^ 2 * (a * M) = a ^ 3 * M := by ring
        _ ≤ B * s * a ^ 2 := hMain
        _ = a ^ 2 * (B * s) := by ring
    have hMinus : 0 ≤ B * s - a * M := sub_nonneg.mpr hReduced
    have hPlus : 0 ≤ B * s + a * M := by positivity
    have hProduct := mul_nonneg hMinus hPlus
    have hSquare : (a * M) ^ 2 ≤ (B * s) ^ 2 := by
      nlinarith [hProduct]
    have hSquareBound : a ^ 2 * M ^ 2 ≤ B ^ 2 * (1 + a ^ 2 * E) := by
      calc
        a ^ 2 * M ^ 2 = (a * M) ^ 2 := by ring
        _ ≤ (B * s) ^ 2 := hSquare
        _ = B ^ 2 * (1 + a ^ 2 * E) := by
          rw [mul_pow, hs2]
    have hOpposite : B ^ 2 * (1 + a ^ 2 * E) < a ^ 2 * M ^ 2 := by
      calc
        B ^ 2 * (1 + a ^ 2 * E) =
            B ^ 2 + a ^ 2 * (B ^ 2 * E) := by ring
        _ < a ^ 2 * (M ^ 2 - B ^ 2 * E) +
              a ^ 2 * (B ^ 2 * E) := by
          exact add_lt_add_left hLarge (a ^ 2 * (B ^ 2 * E))
        _ = a ^ 2 * M ^ 2 := by ring
    exact (not_lt_of_ge hSquareBound) hOpposite
  · intro hThreshold a ha
    let s : ℝ := Real.sqrt (1 + a ^ 2 * E)
    have hs : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = 1 + a ^ 2 * E :=
      Real.sq_sqrt (by positivity)
    have hSquare : (a * M) ^ 2 ≤ (B * s) ^ 2 := by
      calc
        (a * M) ^ 2 = a ^ 2 * M ^ 2 := by ring
        _ ≤ a ^ 2 * (B ^ 2 * E) :=
          mul_le_mul_of_nonneg_left hThreshold (sq_nonneg _)
        _ = B ^ 2 * (a ^ 2 * E) := by ring
        _ ≤ B ^ 2 * (1 + a ^ 2 * E) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
        _ = (B * s) ^ 2 := by rw [mul_pow, hs2]
    have hLeft : 0 ≤ a * M := by positivity
    have hRight : 0 ≤ B * s := by positivity
    have hReduced : a * M ≤ B * s := by
      nlinarith [hSquare]
    calc
      a ^ 3 * M = a ^ 2 * (a * M) := by ring
      _ ≤ a ^ 2 * (B * s) :=
        mul_le_mul_of_nonneg_left hReduced (sq_nonneg _)
      _ = B * Real.sqrt (1 + a ^ 2 * E) * a ^ 2 := by
        dsimp [s]
        ring

/-- For ANY real Schwartz velocity with positive first monomial, a
critical-half bound on all its positive amplitudes forces the precise
base-energy/base-dissipation coefficient threshold. This is a necessary
condition, not an assumed positivity of the energy or dissipation. -/
theorem lowNormalRealSchwartz_criticalHalf_coefficient_necessary
    (f : A3 → SchwartzMap V3 ℝ)
    (hM : 0 < lowNormalRealSchwartzPoint3Monomial f)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ a : ℝ, 0 < a →
      lowNormalRealSchwartzPoint3Monomial (fun j => a • f j) ≤
        C * (1 + |lowNormalRealSchwartzH3EnergyQuadratic
            (fun j => a • f j)|) ^ (1 / 2 : ℝ) *
          |lowNormalRealSchwartzH3TopDissipation
            (fun j => a • f j)|) :
    (lowNormalRealSchwartzPoint3Monomial f) ^ 2 ≤
      (C * |lowNormalRealSchwartzH3TopDissipation f|) ^ 2 *
        |lowNormalRealSchwartzH3EnergyQuadratic f| := by
  apply (criticalHalfEnergyRayBound_iff
    (lowNormalRealSchwartzPoint3Monomial f)
    |lowNormalRealSchwartzH3EnergyQuadratic f|
    (C * |lowNormalRealSchwartzH3TopDissipation f|)
    hM (abs_nonneg _) (mul_nonneg hC (abs_nonneg _))).mp
  intro a ha
  have hh := hBound a ha
  rw [lowNormalRealSchwartzPoint3Monomial_real_smul,
    lowNormalRealSchwartzH3EnergyQuadratic_real_smul,
    lowNormalRealSchwartzH3TopDissipation_real_smul] at hh
  simp only [abs_mul, abs_of_nonneg (sq_nonneg a)] at hh
  calc
    a ^ 3 * lowNormalRealSchwartzPoint3Monomial f ≤
        C * (1 + a ^ 2 * |lowNormalRealSchwartzH3EnergyQuadratic f|) ^
          (1 / 2 : ℝ) *
        (a ^ 2 * |lowNormalRealSchwartzH3TopDissipation f|) := hh
    _ = (C * |lowNormalRealSchwartzH3TopDissipation f|) *
          Real.sqrt (1 + a ^ 2 * |lowNormalRealSchwartzH3EnergyQuadratic f|) *
          a ^ 2 := by
      rw [Real.sqrt_eq_rpow]
      ring

/-- The constructed solenoidal quarter packet supplies a *positive*
physical 243-slot witness at which any putative critical-half uniform
coefficient must satisfy the exact squared threshold. This does not
assert such a coefficient exists for all Schwartz velocities. -/
theorem lowNormalQuarter_exists_criticalHalf_coefficient_threshold :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      0 < lowNormalRealSchwartzPoint3Monomial
        (lowNormalQuarterOppositeSchwartzVelocity ρ hρ) ∧
      ∀ C : ℝ, 0 ≤ C →
        (∀ a : ℝ, 0 < a →
          lowNormalRealSchwartzPoint3Monomial
            (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j) ≤
          C * (1 + |lowNormalRealSchwartzH3EnergyQuadratic
            (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j)|) ^
              (1 / 2 : ℝ) *
            |lowNormalRealSchwartzH3TopDissipation
              (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j)|) →
        (lowNormalRealSchwartzPoint3Monomial
          (lowNormalQuarterOppositeSchwartzVelocity ρ hρ)) ^ 2 ≤
        (C * |lowNormalRealSchwartzH3TopDissipation
          (lowNormalQuarterOppositeSchwartzVelocity ρ hρ)|) ^ 2 *
          |lowNormalRealSchwartzH3EnergyQuadratic
            (lowNormalQuarterOppositeSchwartzVelocity ρ hρ)| := by
  obtain ⟨ρ, hρ, _, hM⟩ :=
    lowNormalQuarterPoint3_exists_both_firstMonomial_signs
  refine ⟨ρ, hρ, hM, ?_⟩
  intro C hC hBound
  exact lowNormalRealSchwartz_criticalHalf_coefficient_necessary
    (lowNormalQuarterOppositeSchwartzVelocity ρ hρ) hM C hC hBound

end
end PrimeTensor.FirstMonomialTriad
