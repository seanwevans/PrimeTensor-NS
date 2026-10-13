import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowRealityPhase
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadFourier

/-!
# Actual seven-derivative phase and cyclic shell bookkeeping

The physical first-monomial Fourier multiplier has phase `(2πi)^7`, which
is `-(2π)^7 i`, rather than the positive `i` used in the preceding symbolic
audit. The reflected low-normal pair consequently has a negative REAL
contribution after insertion of that exact multiplier.

A separate algebraic identity identifies the full six-order symbol with the
three cyclic evaluations of the already-established shell kernel of ONE
common divergence-free Fourier polarization field. No claim that a Schwartz
field realizes the sharp pointwise example, or that its integral has a fixed
sign, is made here.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- The exact physical seven-derivative phase applied to the reflected
low-normal pair. This is still a pointwise symbol, not a PDE energy integral. -/
def lowNormalAuditPhysicalPhasePair (t : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) ^ 7 * lowNormalAuditRealityPair t

private theorem ofReal_mul_re (r : ℝ) (z : ℂ) :
    ((r : ℂ) * z).re = r * z.re := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- The project-wide Fourier convention changes the sign of the earlier
positive-`I` algebraic audit, and fixes the physical normalization. -/
theorem lowNormalAuditPhysicalPhasePair_re (t : ℝ) :
    (lowNormalAuditPhysicalPhasePair t).re =
      -(2 * Real.pi) ^ 7 * (2 * t ^ 2 * (1 + 2 * t) ^ 2) := by
  unfold lowNormalAuditPhysicalPhasePair
  rw [PrimeTensor.Bridge.Euclidean.h3FirstMonomial_fourier_phase]
  have hRearrange :
      -(Complex.I * (((2 * Real.pi) ^ 7 : ℝ) : ℂ)) * lowNormalAuditRealityPair t =
        -(((((2 * Real.pi) ^ 7 : ℝ) : ℂ)) *
          (Complex.I * lowNormalAuditRealityPair t)) := by
    ring
  rw [hRearrange, Complex.neg_re, ofReal_mul_re,
    lowNormalAuditRealityPair_I_re]
  ring

/-- The physical Fourier phase has a nonpositive real part on this explicit
reflected family; the statement is NOT about the integrated PDE term. -/
theorem lowNormalAuditPhysicalPhasePair_nonpos (t : ℝ) :
    (lowNormalAuditPhysicalPhasePair t).re ≤ 0 := by
  rw [lowNormalAuditPhysicalPhasePair_re]
  have hp : 0 ≤ (2 * Real.pi) ^ 7 := by positivity
  have ht : 0 ≤ 2 * t ^ 2 * (1 + 2 * t) ^ 2 := by positivity
  nlinarith [mul_nonneg hp ht]

/-- Its real magnitude retains the sharp quadratic low-frequency scale. -/
theorem lowNormalAuditPhysicalPhasePair_abs_lower (t : ℝ) (ht : 0 ≤ t) :
    (2 * Real.pi) ^ 7 * (2 * t ^ 2) ≤
      |(lowNormalAuditPhysicalPhasePair t).re| := by
  rw [lowNormalAuditPhysicalPhasePair_re]
  have hp : 0 ≤ (2 * Real.pi) ^ 7 := by positivity
  have hx : 0 ≤ (2 * Real.pi) ^ 7 * (2 * t ^ 2 * (1 + 2 * t) ^ 2) := by
    positivity
  rw [neg_mul, abs_neg, abs_of_nonneg hx]
  have h := lowNormalAuditRealityPair_I_re_lower t ht
  rw [lowNormalAuditRealityPair_I_re] at h
  exact mul_le_mul_of_nonneg_left h hp

/-- Even the correct physical normalization cannot restore a uniform
pointwise quadratic-separation bound. This is not an integrated obstruction. -/
theorem lowNormalAudit_no_uniform_physical_phase_quadratic_bound
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      frequencyNorm (lowNormalAuditQ t) ≤
        (2 * t) * min (frequencyNorm lowNormalAuditP) (frequencyNorm (lowNormalAuditR t)) ∧
      K * lowNormalAuditQuadraticWeight t <
        |(lowNormalAuditPhysicalPhasePair t).re| := by
  let C : ℝ := (2 * Real.pi) ^ 7
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0 : C ≠ 0 := ne_of_gt hC
  obtain ⟨t, ht, ht1, hLow, hSharp⟩ :=
    lowNormalAudit_no_uniform_quadratic_reality_phase_bound
      (K / C) (div_nonneg hK hC.le)
  refine ⟨t, ht, ht1, hLow, ?_⟩
  have hScaled := mul_lt_mul_of_pos_left hSharp hC
  have hCancel : C * (K / C) = K := by
    field_simp [hC0] <;> ring
  have hAbs : |(lowNormalAuditPhysicalPhasePair t).re| =
      C * (Complex.I * lowNormalAuditRealityPair t).re := by
    rw [lowNormalAuditPhysicalPhasePair_re, neg_mul]
    change |-(C * (2 * t ^ 2 * (1 + 2 * t) ^ 2))| =
      C * (Complex.I * lowNormalAuditRealityPair t).re
    rw [abs_neg, abs_of_nonneg (mul_nonneg hC.le (by positivity))]
    rw [lowNormalAuditRealityPair_I_re]
  calc
    K * lowNormalAuditQuadraticWeight t =
        C * ((K / C) * lowNormalAuditQuadraticWeight t) := by
          rw [← mul_assoc, hCancel]
    _ < C * (Complex.I * lowNormalAuditRealityPair t).re := hScaled
    _ = |(lowNormalAuditPhysicalPhasePair t).re| := hAbs.symm

/-- At one divergence-free Fourier polarization field, the sum of the three
cyclic shell evaluations is exactly the six-order algebraic coefficient.
This is the pointwise identity needed before any measure-preserving cyclic
reindexing of the TWO-variable Schwartz integral can be attempted. -/
theorem shellKernel_three_cyclic_eq_sixOrder
    (U : (Fin 3 → ℝ) → (Fin 3 → ℂ))
    (p q r : Fin 3 → ℝ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hDiv : ∀ ξ, mixedDot ξ (U ξ) = 0) :
    shellKernel U (p, r) + shellKernel U (p, q) + shellKernel U (q, r) =
      sixOrderTriadCoefficient p q r (U p) (U q) (U r) := by
  have hpr : middleFrequency p r = q := by
    funext i
    dsimp [middleFrequency]
    linarith [hm i]
  have hpq : middleFrequency p q = r := by
    funext i
    dsimp [middleFrequency]
    linarith [hm i]
  have hqr : middleFrequency q r = p := by
    funext i
    dsimp [middleFrequency]
    linarith [hm i]
  change
    complexShellCoefficient p (middleFrequency p r) r (U (middleFrequency p r)) *
      amplitudeDot (U p) (U r) +
    complexShellCoefficient p (middleFrequency p q) q (U (middleFrequency p q)) *
      amplitudeDot (U p) (U q) +
    complexShellCoefficient q (middleFrequency q r) r (U (middleFrequency q r)) *
      amplitudeDot (U q) (U r) =
    sixOrderTriadCoefficient p q r (U p) (U q) (U r)
  rw [hpr, hpq, hqr]
  exact (sixOrderTriadCoefficient_eq_shells p q r (U p) (U q) (U r)
    hm (hDiv p) (hDiv q) (hDiv r)).symm

end
end PrimeTensor.FirstMonomialTriad
