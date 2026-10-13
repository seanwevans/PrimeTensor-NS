import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowSharpness

/-!
# Reality-pair and odd Fourier-phase audit of the sharp low triad

The exact low-normal symbol in `FirstMonomialTriadLowSharpness` is purely
imaginary. Its opposite-frequency, conjugated-amplitude partner has the same
imaginary value. Their raw sum therefore has zero real part, but the real
part after multiplication by `Complex.I` is nonzero and remains of quadratic
order in the low-frequency parameter.

These are finite-dimensional algebraic statements. A physical H3 energy
identity would additionally require proving the Fourier phase, integral
representation, and normalization of the relevant PDE term.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- The opposite-frequency/conjugated-amplitude symbol from the sharpness
example. In this example the conjugates of A and B equal themselves, while
the conjugate of C is its negative. -/
def lowNormalAuditReflectedCoefficient (t : ℝ) : ℂ :=
  sixOrderTriadCoefficient (fun i => -lowNormalAuditP i)
    (fun i => -lowNormalAuditQ t i) (fun i => -lowNormalAuditR t i)
    lowNormalAuditA lowNormalAuditB (fun i => -lowNormalAuditC i)

/-- Exact opposite-frequency pair, without the Fourier derivative phase. -/
def lowNormalAuditRealityPair (t : ℝ) : ℂ :=
  sixOrderTriadCoefficient lowNormalAuditP (lowNormalAuditQ t) (lowNormalAuditR t)
    lowNormalAuditA lowNormalAuditB lowNormalAuditC +
  lowNormalAuditReflectedCoefficient t

/-- The reality pair doubles, rather than cancels, the imaginary symbol. -/
theorem lowNormalAuditRealityPair_eq (t : ℝ) :
    lowNormalAuditRealityPair t =
      -(2 : ℂ) * ((t^2 * (1+2*t)^2 : ℝ) : ℂ) * Complex.I := by
  unfold lowNormalAuditRealityPair lowNormalAuditReflectedCoefficient
  rw [lowNormalAudit_sixOrder, lowNormalAudit_reflected_sixOrder]
  ring

/-- The bare pair has no real contribution; the missing odd-derivative
Fourier multiplier cannot be dropped in an energy-sign audit. -/
theorem lowNormalAuditRealityPair_re (t : ℝ) :
    (lowNormalAuditRealityPair t).re = 0 := by
  rw [lowNormalAuditRealityPair_eq]
  have hCast :
      -(2 : ℂ) * ((t^2 * (1+2*t)^2 : ℝ) : ℂ) =
        ((-2 * t^2 * (1+2*t)^2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hCast]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- Multiplication by the symbolic odd-derivative phase `I` converts the
imaginary pair to a positive real number. No physical Fourier identity is
claimed here. -/
theorem lowNormalAuditRealityPair_I_re (t : ℝ) :
    (Complex.I * lowNormalAuditRealityPair t).re =
      2 * t^2 * (1+2*t)^2 := by
  rw [lowNormalAuditRealityPair_eq]
  have h :
      Complex.I * (-(2 : ℂ) * ((t^2 * (1+2*t)^2 : ℝ) : ℂ) * Complex.I) =
        (2 : ℂ) * ((t^2 * (1+2*t)^2 : ℝ) : ℂ) := by
    calc
      _ = -(2 : ℂ) * ((t^2 * (1+2*t)^2 : ℝ) : ℂ) *
          (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [h]
  have hCast :
      (2 : ℂ) * ((t^2 * (1+2*t)^2 : ℝ) : ℂ) =
        ((2 * t^2 * (1+2*t)^2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hCast]
  exact Complex.ofReal_re _

/-- The phase-adjusted real contribution is at least twice the leading
quadratic low-frequency scale for nonnegative t. -/
theorem lowNormalAuditRealityPair_I_re_lower (t : ℝ) (ht : 0 ≤ t) :
    2 * t^2 ≤ (Complex.I * lowNormalAuditRealityPair t).re := by
  rw [lowNormalAuditRealityPair_I_re]
  have h : (1 : ℝ) ≤ (1+2*t)^2 := by nlinarith [sq_nonneg t]
  calc
    2 * t^2 = (2 * t^2) * 1 := by ring
    _ ≤ (2 * t^2) * (1+2*t)^2 :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * t^2 * (1+2*t)^2 := by ring

/-- Even after explicitly pairing the reality partner and inserting the
phase I, the pointwise coefficient violates a uniform quadratic-separation
bound for this family. This does not establish an integrated PDE obstruction. -/
theorem lowNormalAudit_no_uniform_quadratic_reality_phase_bound
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      frequencyNorm (lowNormalAuditQ t) ≤
        (2*t) * min (frequencyNorm lowNormalAuditP) (frequencyNorm (lowNormalAuditR t)) ∧
      K * lowNormalAuditQuadraticWeight t <
        (Complex.I * lowNormalAuditRealityPair t).re := by
  obtain ⟨t, ht, ht1, hLow, hSharp⟩ :=
    lowNormalAudit_no_uniform_quadratic_bound K hK
  refine ⟨t, ht, ht1, hLow, ?_⟩
  calc
    K * lowNormalAuditQuadraticWeight t <
        ‖sixOrderTriadCoefficient lowNormalAuditP (lowNormalAuditQ t) (lowNormalAuditR t)
          lowNormalAuditA lowNormalAuditB lowNormalAuditC‖ := hSharp
    _ = t^2 * (1+2*t)^2 := lowNormalAudit_coefficient_norm t
    _ ≤ 2 * t^2 * (1+2*t)^2 := by
      have h : 0 ≤ t^2 * (1+2*t)^2 :=
        mul_nonneg (sq_nonneg t) (sq_nonneg (1+2*t))
      linarith
    _ = (Complex.I * lowNormalAuditRealityPair t).re :=
      (lowNormalAuditRealityPair_I_re t).symm

end
end PrimeTensor.FirstMonomialTriad
