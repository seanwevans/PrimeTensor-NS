import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadReconstruction

/-!
# Collinear triads vanish without a frame or inverse frequency

For frequencies s*v, t*v, u*v, middle-frequency incompressibility forces
an individual ordered coefficient to vanish. If t is zero, the differentiated
middle-frequency factor is zero; otherwise the polarization is perpendicular
to v. This includes zero frequencies and works in any finite dimension.
-/

namespace PrimeTensor.FirstMonomialTriad

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem dot_line_frequencies (v : ι → ℝ) (s t : ℝ) :
    dot (fun i => s * v i) (fun i => t * v i) = (s * t) * dot v v := by
  unfold dot
  calc
    ∑ i, s * v i * (t * v i) = ∑ i, (s * t) * (v i * v i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (s * t) * ∑ i, v i * v i := (Finset.mul_sum _ _ _).symm

theorem mixedDot_line_frequency (v : ι → ℝ) (t : ℝ) (b : ι → ℂ) :
    mixedDot (fun i => t * v i) b = (t : ℂ) * mixedDot v b := by
  simp [mixedDot, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]

/-- Each ordered coefficient vanishes on a frequency line. No momentum
hypothesis, nonzero frequency, or normal direction is required. -/
theorem complexCoefficient_collinear (v : ι → ℝ) (s t u : ℝ) (b : ι → ℂ)
    (hDiv : mixedDot (fun i => t * v i) b = 0) :
    complexCoefficient (fun i => s * v i) (fun i => t * v i)
      (fun i => u * v i) b = 0 := by
  rw [mixedDot_line_frequency] at hDiv
  simp only [complexCoefficient, dot_line_frequencies, mixedDot_line_frequency]
  push_cast
  rcases mul_eq_zero.mp hDiv with ht | hb
  · simp [ht]
  · simp [hb]

/-- Collinear incompressible triads vanish term by term, hence also after
summing all six orderings. The line parameters may be zero. -/
theorem sixOrderTriadCoefficient_collinear (v : ι → ℝ) (s t u : ℝ)
    (a b c : ι → ℂ)
    (ha : mixedDot (fun i => s * v i) a = 0)
    (hb : mixedDot (fun i => t * v i) b = 0)
    (hc : mixedDot (fun i => u * v i) c = 0) :
    sixOrderTriadCoefficient (fun i => s * v i) (fun i => t * v i)
      (fun i => u * v i) a b c = 0 := by
  simp only [sixOrderTriadCoefficient, orderedTriadCoefficient,
    complexCoefficient_collinear v s t u b hb,
    complexCoefficient_collinear v s u t c hc,
    complexCoefficient_collinear v t s u a ha,
    complexCoefficient_collinear v t u s c hc,
    complexCoefficient_collinear v u s t a ha,
    complexCoefficient_collinear v u t s b hb,
    zero_mul, zero_add]

/-- The momentum-conserving triad (0,q,-q) is included, with no constraint
on its zero-frequency amplitude. -/
theorem sixOrderTriadCoefficient_zero_frequency (q : ι → ℝ) (a b c : ι → ℂ)
    (hb : mixedDot q b = 0) (hc : mixedDot (fun i => -q i) c = 0) :
    sixOrderTriadCoefficient (fun _ => 0) q (fun i => -q i) a b c = 0 := by
  have ha : mixedDot (fun i => (0 : ℝ) * q i) a = 0 := by
    simp [mixedDot]
  have hb' : mixedDot (fun i => (1 : ℝ) * q i) b = 0 := by
    simpa only [one_mul] using hb
  have hc' : mixedDot (fun i => (-1 : ℝ) * q i) c = 0 := by
    simpa only [neg_one_mul] using hc
  simpa only [zero_mul, one_mul, neg_one_mul] using
    sixOrderTriadCoefficient_collinear q 0 1 (-1) a b c ha hb' hc'

/-- A zero first frequency and momentum conservation force the preceding
zero-frequency configuration. -/
theorem sixOrderTriadCoefficient_zero_of_first_frequency_zero
    (p q r : ι → ℝ) (a b c : ι → ℂ)
    (hp : p = fun _ => 0) (hMomentum : ∀ i, p i + q i + r i = 0)
    (hb : mixedDot q b = 0) (hc : mixedDot r c = 0) :
    sixOrderTriadCoefficient p q r a b c = 0 := by
  have hr : r = fun i => -q i := by
    funext i
    have h := hMomentum i
    rw [hp] at h
    dsimp at h
    linarith
  rw [hp, hr]
  apply sixOrderTriadCoefficient_zero_frequency q a b c hb
  rw [← hr]
  exact hc

end
end PrimeTensor.FirstMonomialTriad
