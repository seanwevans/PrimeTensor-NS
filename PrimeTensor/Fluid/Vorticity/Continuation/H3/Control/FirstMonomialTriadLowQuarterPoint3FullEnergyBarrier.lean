import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3AmplitudeScaling

/-!
# Cubic first-monomial obstruction to fixed full-H3 quadratic absorption

The preceding commit proved that the complete signed physical first monomial
scales cubically, while fourth-derivative dissipation scales quadratically.
Here the same comparison is made against ALL FOUR orders of the componentwise
H3 energy (zeroth through third), not just the top dissipation form.

A generic result first shows that a positive cubic Schwartz witness escapes
*any* quadratic homogeneous budget, even after an arbitrary additive real
constant. The concrete corollary takes the full unnormalized H3 Schwartz
energy plus fourth-derivative dissipation, with independent coefficients.
The additive constant covers the normalization 1 in `velocityH3EnergyAt`.

This is a counterexample to velocity-independent *linear* absorption only.
It neither rules out nonlinear/energy-dependent interpolation estimates nor
claims a Navier--Stokes solution, loss of smoothness, or blowup.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterFullEnergy (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Zeroth derivative energy, transported to the real Schwartz carrier. -/
noncomputable def lowNormalRealSchwartzH3Square0
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∫ x : V3, (f j x) ^ 2

/-- First derivative energy, with the complete ordered coordinate sum. -/
noncomputable def lowNormalRealSchwartzH3Square1
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∫ x : V3,
    ((∂_{h3FourierAxisDirection i} (f j)) x) ^ 2

/-- Second derivative energy, with all two-derivative coordinate slots. -/
noncomputable def lowNormalRealSchwartzH3Square2
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∫ x : V3,
    ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k} (f j))) x) ^ 2

/-- Third derivative energy, with all three-derivative coordinate slots. -/
noncomputable def lowNormalRealSchwartzH3Square3
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∫ x : V3,
    ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k}
        (∂_{h3FourierAxisDirection l} (f j)))) x) ^ 2

/-- Exactly the quadratic part of canonical componentwise H3 energy, on
Schwartz components. The canonical path energy adds the constant 1. -/
noncomputable def lowNormalRealSchwartzH3EnergyQuadratic
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  lowNormalRealSchwartzH3Square0 f +
    lowNormalRealSchwartzH3Square1 f +
    lowNormalRealSchwartzH3Square2 f +
    lowNormalRealSchwartzH3Square3 f

/-- All zeroth-order L2 components have exact quadratic amplitude scaling. -/
theorem lowNormalRealSchwartzH3Square0_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Square0 (fun j => a • f j) =
      a ^ 2 * lowNormalRealSchwartzH3Square0 f := by
  unfold lowNormalRealSchwartzH3Square0
  simp only [smul_apply, smul_eq_mul, mul_pow, integral_const_mul,
    ← Finset.mul_sum]

/-- The entire first-order derivative quadratic form is degree two. -/
theorem lowNormalRealSchwartzH3Square1_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Square1 (fun j => a • f j) =
      a ^ 2 * lowNormalRealSchwartzH3Square1 f := by
  unfold lowNormalRealSchwartzH3Square1
  simp only [LineDeriv.lineDerivOp_smul, smul_apply, smul_eq_mul,
    mul_pow, integral_const_mul, ← Finset.mul_sum]

/-- The entire second-order derivative quadratic form is degree two. -/
theorem lowNormalRealSchwartzH3Square2_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Square2 (fun j => a • f j) =
      a ^ 2 * lowNormalRealSchwartzH3Square2 f := by
  unfold lowNormalRealSchwartzH3Square2
  simp only [LineDeriv.lineDerivOp_smul, smul_apply, smul_eq_mul,
    mul_pow, integral_const_mul, ← Finset.mul_sum]

/-- The entire third-order derivative quadratic form is degree two. -/
theorem lowNormalRealSchwartzH3Square3_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Square3 (fun j => a • f j) =
      a ^ 2 * lowNormalRealSchwartzH3Square3 f := by
  unfold lowNormalRealSchwartzH3Square3
  simp only [LineDeriv.lineDerivOp_smul, smul_apply, smul_eq_mul,
    mul_pow, integral_const_mul, ← Finset.mul_sum]

/-- The FULL unnormalized H3 energy scales quadratically, with no derivative
order omitted. -/
theorem lowNormalRealSchwartzH3EnergyQuadratic_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3EnergyQuadratic (fun j => a • f j) =
      a ^ 2 * lowNormalRealSchwartzH3EnergyQuadratic f := by
  unfold lowNormalRealSchwartzH3EnergyQuadratic
  rw [lowNormalRealSchwartzH3Square0_real_smul,
    lowNormalRealSchwartzH3Square1_real_smul,
    lowNormalRealSchwartzH3Square2_real_smul,
    lowNormalRealSchwartzH3Square3_real_smul]
  ring

/-- Abstract sharpness: an explicitly realized positive cubic first monomial
outgrows EVERY homogeneous quadratic functional, including an additive
constant. The quadratic functional is *arbitrary* (not assumed nonnegative). -/
theorem lowNormalQuarter_exists_amplitude_exceeding_quadratic_plus_constant
    (Q : (A3 → SchwartzMap V3 ℝ) → ℝ)
    (hQ : ∀ (a : ℝ) (f : A3 → SchwartzMap V3 ℝ),
      Q (fun j => a • f j) = a ^ 2 * Q f)
    (C K : ℝ) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ a : ℝ, 0 < a ∧
      C * Q (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j) + K <
      lowNormalRealSchwartzPoint3Monomial
        (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j) := by
  obtain ⟨ρ, hρ, _, hPos⟩ := lowNormalQuarterPoint3_exists_both_firstMonomial_signs
  let f : A3 → SchwartzMap V3 ℝ := lowNormalQuarterOppositeSchwartzVelocity ρ hρ
  let M : ℝ := lowNormalRealSchwartzPoint3Monomial f
  let B : ℝ := C * Q f
  have hM : 0 < M := hPos
  let a : ℝ := (|B| + |K| + 1) / M + 1
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha1 : 1 ≤ a := by
    dsimp [a]
    have hNonneg : 0 ≤ (|B| + |K| + 1) / M :=
      div_nonneg (by positivity) hM.le
    linarith
  have ha2 : 1 ≤ a ^ 2 := by
    nlinarith [sq_nonneg (a - 1)]
  have hFormula : a * M = |B| + |K| + 1 + M := by
    change ((|B| + |K| + 1) / M + 1) * M = _
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hM), one_mul]
  have hStrict : B + |K| < a * M := by
    rw [hFormula]
    have hAbs := le_abs_self B
    linarith
  have hK : K ≤ a ^ 2 * |K| := by
    calc
      K ≤ |K| := le_abs_self K
      _ = 1 * |K| := by ring
      _ ≤ a ^ 2 * |K| := mul_le_mul_of_nonneg_right ha2 (abs_nonneg K)
  have hAmplified := mul_lt_mul_of_pos_left hStrict (pow_pos ha 2)
  have hBudget : a ^ 2 * B + K < a ^ 3 * M := by
    calc
      a ^ 2 * B + K ≤ a ^ 2 * B + a ^ 2 * |K| := by
        exact add_le_add (le_refl (a ^ 2 * B)) hK
      _ = a ^ 2 * (B + |K|) := by ring
      _ < a ^ 2 * (a * M) := hAmplified
      _ = a ^ 3 * M := by ring
  refine ⟨ρ, hρ, a, ha, ?_⟩
  change C * Q (fun j : A3 => a • f j) + K <
    lowNormalRealSchwartzPoint3Monomial (fun j : A3 => a • f j)
  rw [hQ a f, lowNormalRealSchwartzPoint3Monomial_real_smul]
  change C * (a ^ 2 * Q f) + K < a ^ 3 * M
  calc
    C * (a ^ 2 * Q f) + K = a ^ 2 * B + K := by dsimp [B]; ring
    _ < a ^ 3 * M := hBudget

/-- No fixed weighted combination of the full quadratic H3 energy, top
quadratic dissipation, and energy normalization 1 absorbs the *positive*
complete 243-slot physical monomial for all real solenoidal Schwartz data.
The two coefficients can be arbitrary real numbers. -/
theorem lowNormalQuarter_exists_amplitude_exceeding_fullH3_absorption
    (ε C : ℝ) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ a : ℝ, 0 < a ∧
      ε * lowNormalRealSchwartzH3TopDissipation
          (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j) +
        C * (1 + lowNormalRealSchwartzH3EnergyQuadratic
          (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j)) <
      lowNormalRealSchwartzPoint3Monomial
        (fun j : A3 => a • lowNormalQuarterOppositeSchwartzVelocity ρ hρ j) := by
  let Q : (A3 → SchwartzMap V3 ℝ) → ℝ := fun f =>
    ε * lowNormalRealSchwartzH3TopDissipation f +
      C * lowNormalRealSchwartzH3EnergyQuadratic f
  have hQ : ∀ (a : ℝ) (f : A3 → SchwartzMap V3 ℝ),
      Q (fun j => a • f j) = a ^ 2 * Q f := by
    intro a f
    change ε * lowNormalRealSchwartzH3TopDissipation (fun j => a • f j) +
        C * lowNormalRealSchwartzH3EnergyQuadratic (fun j => a • f j) =
      a ^ 2 * (ε * lowNormalRealSchwartzH3TopDissipation f +
        C * lowNormalRealSchwartzH3EnergyQuadratic f)
    rw [lowNormalRealSchwartzH3TopDissipation_real_smul,
      lowNormalRealSchwartzH3EnergyQuadratic_real_smul]
    ring
  obtain ⟨ρ, hρ, a, ha, hEscape⟩ :=
    lowNormalQuarter_exists_amplitude_exceeding_quadratic_plus_constant Q hQ 1 C
  refine ⟨ρ, hρ, a, ha, ?_⟩
  have hEq : ∀ f : A3 → SchwartzMap V3 ℝ,
      ε * lowNormalRealSchwartzH3TopDissipation f +
        C * (1 + lowNormalRealSchwartzH3EnergyQuadratic f) = Q f + C := by
    intro f
    dsimp [Q]
    ring
  rw [hEq]
  simpa only [one_mul] using hEscape

end
end PrimeTensor.FirstMonomialTriad
