import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowSeparation

/-!
# Polynomial solenoidal germs at the six sharp low-normal frequencies

Instead of dividing by the varying frequency squared, use the polynomial
transverse lift

    P_ξ(a) = (ξ · ξ) a - (ξ · a) ξ.

This is solenoidal even at ξ = 0.  Division only by a *fixed center*
frequency squared recovers each prescribed transverse polarization at its
nonzero center.  The polynomial lift respects the Fourier reality involution:
reversing frequency and conjugating amplitude conjugates the output.

The germs below are not Schwartz functions: compactly supported scalar bumps
and their disjoint six-packet assembly are separate subsequent steps.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- Squared Euclidean frequency radius viewed as a complex number. -/
def lowNormalComplexSquaredRadius (ξ : Fin 3 → ℝ) : ℂ :=
  mixedDot ξ (fun d => (ξ d : ℂ))

/-- The polynomial, everywhere-defined divergence-free Fourier lift. -/
def lowNormalPolynomialSolenoidalLift
    (ξ : Fin 3 → ℝ) (a : Fin 3 → ℂ) (d : Fin 3) : ℂ :=
  lowNormalComplexSquaredRadius ξ * a d -
    mixedDot ξ a * (ξ d : ℂ)

/-- The lift has zero Fourier divergence for every frequency, including zero. -/
theorem lowNormalPolynomialSolenoidalLift_divergence
    (ξ : Fin 3 → ℝ) (a : Fin 3 → ℂ) :
    mixedDot ξ (lowNormalPolynomialSolenoidalLift ξ a) = 0 := by
  simp [mixedDot, lowNormalPolynomialSolenoidalLift,
    lowNormalComplexSquaredRadius, Fin.sum_univ_succ]
  ring

/-- At a transverse center, the lift simply multiplies by its squared radius. -/
theorem lowNormalPolynomialSolenoidalLift_at_transverse
    (η : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (ha : mixedDot η a = 0) :
    lowNormalPolynomialSolenoidalLift η a =
      fun d => lowNormalComplexSquaredRadius η * a d := by
  funext d
  simp [lowNormalPolynomialSolenoidalLift, ha]

/-- Reflection and complex conjugation commute with the polynomial lift.
The operation `star` is the complex conjugation supplied by Mathlib. -/
theorem lowNormalPolynomialSolenoidalLift_reality
    (ξ : Fin 3 → ℝ) (a : Fin 3 → ℂ) :
    lowNormalPolynomialSolenoidalLift (fun d => -ξ d)
        (fun d => star (a d)) =
      fun d => star (lowNormalPolynomialSolenoidalLift ξ a d) := by
  funext d
  change lowNormalPolynomialSolenoidalLift (fun k => -ξ k)
      (fun k => (starRingEnd ℂ) (a k)) d =
    (starRingEnd ℂ) (lowNormalPolynomialSolenoidalLift ξ a d)
  simp [lowNormalPolynomialSolenoidalLift, lowNormalComplexSquaredRadius,
    mixedDot, Fin.sum_univ_succ, map_add, map_sub, map_mul,
    Complex.conj_ofReal] <;> ring

/-- Normalize by the fixed anchor, never by the varying frequency. -/
def lowNormalNormalizedSolenoidalGerm
    (η ξ : Fin 3 → ℝ) (a : Fin 3 → ℂ) (d : Fin 3) : ℂ :=
  lowNormalPolynomialSolenoidalLift ξ a d / lowNormalComplexSquaredRadius η

/-- Normalized polynomial germs remain divergence-free everywhere. -/
theorem lowNormalNormalizedSolenoidalGerm_divergence
    (η ξ : Fin 3 → ℝ) (a : Fin 3 → ℂ) :
    mixedDot ξ (lowNormalNormalizedSolenoidalGerm η ξ a) = 0 := by
  simp [mixedDot, lowNormalNormalizedSolenoidalGerm,
    lowNormalPolynomialSolenoidalLift, lowNormalComplexSquaredRadius,
    Fin.sum_univ_succ]
  ring

/-- Every transverse amplitude is reproduced at a nonzero fixed anchor. -/
theorem lowNormalNormalizedSolenoidalGerm_at_center
    (η : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (ha : mixedDot η a = 0)
    (hr : lowNormalComplexSquaredRadius η ≠ 0) :
    lowNormalNormalizedSolenoidalGerm η η a = a := by
  funext d
  simp only [lowNormalNormalizedSolenoidalGerm,
    lowNormalPolynomialSolenoidalLift, ha, zero_mul, sub_zero]
  field_simp [hr]

/-- The sharp family's first frequency has unit squared radius. -/
theorem lowNormalAuditP_complex_radius :
    lowNormalComplexSquaredRadius lowNormalAuditP = 1 := by
  norm_num [lowNormalComplexSquaredRadius, mixedDot,
    lowNormalAuditP, Fin.sum_univ_succ]

/-- Its small middle frequency has squared radius 2t². -/
theorem lowNormalAuditQ_complex_radius (t : ℝ) :
    lowNormalComplexSquaredRadius (lowNormalAuditQ t) =
      ((2 * t ^ 2 : ℝ) : ℂ) := by
  norm_num [lowNormalComplexSquaredRadius, mixedDot,
    lowNormalAuditQ, Fin.sum_univ_succ]
  ring

/-- The remaining outer frequency has positive squared radius for t ≠ 0. -/
theorem lowNormalAuditR_complex_radius (t : ℝ) :
    lowNormalComplexSquaredRadius (lowNormalAuditR t) =
      ((1 + 2 * t + 2 * t ^ 2 : ℝ) : ℂ) := by
  norm_num [lowNormalComplexSquaredRadius, mixedDot,
    lowNormalAuditR, Fin.sum_univ_succ]
  ring

/-- The sharp transverse A, B, C amplitudes all have normalized polynomial
extensions, with no frequency-dependent denominator. -/
theorem lowNormalSharpPolarizationGerms_at_centers
    (t : ℝ) (ht : t ≠ 0) :
    lowNormalNormalizedSolenoidalGerm lowNormalAuditP lowNormalAuditP
        lowNormalAuditA = lowNormalAuditA ∧
    lowNormalNormalizedSolenoidalGerm (lowNormalAuditQ t) (lowNormalAuditQ t)
        lowNormalAuditB = lowNormalAuditB ∧
    lowNormalNormalizedSolenoidalGerm (lowNormalAuditR t) (lowNormalAuditR t)
        lowNormalAuditC = lowNormalAuditC := by
  obtain ⟨hA, hB, hC⟩ := lowNormalAudit_incompressible t
  have hP : lowNormalComplexSquaredRadius lowNormalAuditP ≠ 0 := by
    rw [lowNormalAuditP_complex_radius]
    norm_num
  have hQ : lowNormalComplexSquaredRadius (lowNormalAuditQ t) ≠ 0 := by
    rw [lowNormalAuditQ_complex_radius]
    have hn : (2 * t ^ 2 : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)
    exact_mod_cast hn
  have hR : lowNormalComplexSquaredRadius (lowNormalAuditR t) ≠ 0 := by
    rw [lowNormalAuditR_complex_radius]
    have ht2 : 0 < t ^ 2 := by
      exact lt_of_le_of_ne (sq_nonneg t) (Ne.symm (pow_ne_zero 2 ht))
    have hn : (1 + 2 * t + 2 * t ^ 2 : ℝ) ≠ 0 := by
      have hsq := sq_nonneg (1 + t)
      have hp : 0 < (1 + t) ^ 2 + t ^ 2 := by linarith
      have hp' : 0 < (1 + 2 * t + 2 * t ^ 2 : ℝ) := by nlinarith
      exact ne_of_gt hp'
    exact_mod_cast hn
  exact ⟨lowNormalNormalizedSolenoidalGerm_at_center _ _ hA hP,
    lowNormalNormalizedSolenoidalGerm_at_center _ _ hB hQ,
    lowNormalNormalizedSolenoidalGerm_at_center _ _ hC hR⟩

end
end PrimeTensor.FirstMonomialTriad
