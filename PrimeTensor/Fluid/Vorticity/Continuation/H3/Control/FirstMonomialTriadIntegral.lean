import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadCancellation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Complex amplitudes and integrated first-monomial triad cancellation

Use the two outer frequencies p,r as independent variables and put q=-(p+r).
Exchange is then exactly Prod.swap, preserving the product measure. The
integrable complex kernel has twice its integral equal to the integral of
the shell-difference kernel. This matches the physical pairing's factor two.

Integrability and pointwise Fourier incompressibility are explicit inputs.
Identification with the physical derivative pairing is not asserted here.
-/

namespace PrimeTensor
namespace FirstMonomialTriad

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Real frequency contracted with a complex Fourier polarization. -/
def mixedDot (p : ι → ℝ) (b : ι → ℂ) : ℂ :=
  ∑ i, (p i : ℂ) * b i

theorem mixedDot_re (p : ι → ℝ) (b : ι → ℂ) :
    (mixedDot p b).re = dot p (fun i => (b i).re) := by
  simp [mixedDot, dot, Complex.mul_re]

theorem mixedDot_im (p : ι → ℝ) (b : ι → ℂ) :
    (mixedDot p b).im = dot p (fun i => (b i).im) := by
  simp [mixedDot, dot, Complex.mul_im]

/-- Bilinear, not Hermitian: all three frequencies sum to zero. -/
def amplitudeDot (a c : ι → ℂ) : ℂ := ∑ i, a i * c i

theorem amplitudeDot_comm (a c : ι → ℂ) :
    amplitudeDot a c = amplitudeDot c a := by
  unfold amplitudeDot
  apply Finset.sum_congr rfl
  intro i _
  ring

def complexCoefficient (p q r : ι → ℝ) (b : ι → ℂ) : ℂ :=
  ((dot p r * (dot p q) ^ 2 : ℝ) : ℂ) * mixedDot r b

def complexShellCoefficient (p q r : ι → ℝ) (b : ι → ℂ) : ℂ :=
  (dot p r : ℂ) * mixedDot p b * (dot q q : ℂ) *
    ((dot r r - dot p p : ℝ) : ℂ)

/-- Extend the real polynomial identity to actual complex polarizations. -/
theorem complex_exchanged_coefficient
    (p q r : ι → ℝ) (b : ι → ℂ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hDivergence : mixedDot q b = 0) :
    complexCoefficient p q r b + complexCoefficient r q p b =
      complexShellCoefficient p q r b := by
  have hRe : dot q (fun i => (b i).re) = 0 := by
    simpa only [mixedDot_re, Complex.zero_re] using congrArg Complex.re hDivergence
  have hIm : dot q (fun i => (b i).im) = 0 := by
    simpa only [mixedDot_im, Complex.zero_im] using congrArg Complex.im hDivergence
  apply Complex.ext
  · simpa [complexCoefficient, complexShellCoefficient, coefficient, pow_two,
      Complex.mul_re, Complex.mul_im, mixedDot_re, mixedDot_im] using
      exchanged_coefficient p q r (fun i => (b i).re) hMomentum hRe
  · simpa [complexCoefficient, complexShellCoefficient, coefficient, pow_two,
      Complex.mul_re, Complex.mul_im, mixedDot_re, mixedDot_im] using
      exchanged_coefficient p q r (fun i => (b i).im) hMomentum hIm

def middleFrequency (p r : ι → ℝ) : ι → ℝ := fun i => -(p i + r i)

omit [Fintype ι] in
theorem middleFrequency_swap (p r : ι → ℝ) :
    middleFrequency r p = middleFrequency p r := by
  funext i
  simp only [middleFrequency]
  ring

omit [Fintype ι] in
theorem middleFrequency_momentum (p r : ι → ℝ) :
    ∀ i, p i + middleFrequency p r i + r i = 0 := by
  intro i
  simp only [middleFrequency]
  ring

/-- Unsymmetrized triad kernel; derivative constants remain external. -/
def amplitudeKernel (U : (ι → ℝ) → (ι → ℂ))
    (z : (ι → ℝ) × (ι → ℝ)) : ℂ :=
  complexCoefficient z.1 (middleFrequency z.1 z.2) z.2
      (U (middleFrequency z.1 z.2)) * amplitudeDot (U z.1) (U z.2)

/-- The paired kernel, with the outer shell difference retained. -/
def shellKernel (U : (ι → ℝ) → (ι → ℂ))
    (z : (ι → ℝ) × (ι → ℝ)) : ℂ :=
  complexShellCoefficient z.1 (middleFrequency z.1 z.2) z.2
      (U (middleFrequency z.1 z.2)) * amplitudeDot (U z.1) (U z.2)

theorem amplitudeKernel_add_swap
    (U : (ι → ℝ) → (ι → ℂ))
    (hDivergence : ∀ q, mixedDot q (U q) = 0)
    (z : (ι → ℝ) × (ι → ℝ)) :
    amplitudeKernel U z + amplitudeKernel U z.swap = shellKernel U z := by
  rcases z with ⟨p, r⟩
  change
    complexCoefficient p (middleFrequency p r) r (U (middleFrequency p r)) *
        amplitudeDot (U p) (U r) +
      complexCoefficient r (middleFrequency r p) p (U (middleFrequency r p)) *
        amplitudeDot (U r) (U p) =
      complexShellCoefficient p (middleFrequency p r) r (U (middleFrequency p r)) *
        amplitudeDot (U p) (U r)
  rw [middleFrequency_swap p r]
  rw [amplitudeDot_comm (U r) (U p), ← add_mul]
  rw [complex_exchanged_coefficient p (middleFrequency p r) r
    (U (middleFrequency p r)) (middleFrequency_momentum p r)
    (hDivergence (middleFrequency p r))]

variable (μ : Measure (ι → ℝ)) [SFinite μ]

theorem shellKernel_integrable
    (U : (ι → ℝ) → (ι → ℂ))
    (hDivergence : ∀ q, mixedDot q (U q) = 0)
    (hKernel : Integrable (amplitudeKernel U) (μ.prod μ)) :
    Integrable (shellKernel U) (μ.prod μ) := by
  exact (hKernel.add hKernel.swap).congr
    (Filter.Eventually.of_forall (amplitudeKernel_add_swap U hDivergence))

/-- Product-measure exchange cancels the averaging denominator exactly. -/
theorem integral_shellKernel_eq_twice
    (U : (ι → ℝ) → (ι → ℂ))
    (hDivergence : ∀ q, mixedDot q (U q) = 0)
    (hKernel : Integrable (amplitudeKernel U) (μ.prod μ)) :
    (∫ z, shellKernel U z ∂μ.prod μ) =
      2 * ∫ z, amplitudeKernel U z ∂μ.prod μ := by
  calc
    (∫ z, shellKernel U z ∂μ.prod μ) =
        ∫ z, amplitudeKernel U z + amplitudeKernel U z.swap ∂μ.prod μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun z => (amplitudeKernel_add_swap U hDivergence z).symm)
    _ = (∫ z, amplitudeKernel U z ∂μ.prod μ) +
        ∫ z, amplitudeKernel U z.swap ∂μ.prod μ :=
      integral_add hKernel hKernel.swap
    _ = 2 * ∫ z, amplitudeKernel U z ∂μ.prod μ := by
      rw [integral_prod_swap]
      ring

/-- Keep arbitrary Fourier normalization and the physical pairing's factor
two explicit. No identification of the integral with that pairing is assumed. -/
theorem twice_re_integral_eq_re_shell
    (U : (ι → ℝ) → (ι → ℂ)) (c : ℂ)
    (hDivergence : ∀ q, mixedDot q (U q) = 0)
    (hKernel : Integrable (amplitudeKernel U) (μ.prod μ)) :
    2 * (c * ∫ z, amplitudeKernel U z ∂μ.prod μ).re =
      (c * ∫ z, shellKernel U z ∂μ.prod μ).re := by
  rw [integral_shellKernel_eq_twice μ U hDivergence hKernel]
  have h : c * (2 * ∫ z, amplitudeKernel U z ∂μ.prod μ) =
      2 * (c * ∫ z, amplitudeKernel U z ∂μ.prod μ) := by ring
  rw [h]
  simp [Complex.mul_re]

end
end FirstMonomialTriad
end PrimeTensor
