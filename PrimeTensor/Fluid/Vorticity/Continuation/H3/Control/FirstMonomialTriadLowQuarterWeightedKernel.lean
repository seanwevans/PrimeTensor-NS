import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterCoherentOrbitBridge

/-!
# Exact trilinear scaling of the signed first-monomial Fourier kernel

The fixed-width signed kernel has a strictly positive twelve-center tube, but
replacing the three frequency cutoffs by narrower cutoffs changes the field.
A mathematically exact alternative is to multiply the already constructed
real-compatible solenoidal Schwartz Fourier field by ONE real-valued scalar
window. Trilinearity then gives an exact product of three scalar weights.

This module proves that product formula directly from the six ordered
first-monomial symbol, including all six permutations. It does not assume
that shrinking arbitrary packet cutoffs preserves the original kernel.

The resulting sign-transfer theorem is pointwise. Constructing a specific
nonnegative, even, compactly supported window and proving a nonzero global
integral are subsequent steps.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Metric
open scoped Topology SchwartzMap

noncomputable section

private abbrev WeightV := Fin 3 → ℝ
private abbrev WeightA := Fin 3 → ℂ

/-- A real scalar frequency window applied to the original fixed-width
Schwartz field. The window is not assumed nonnegative or even here. -/
def lowNormalQuarterWeightedFourier (w : WeightV → ℝ)
    (ξ : WeightV) : WeightA :=
  fun d => (w ξ : ℂ) * lowNormalQuarterSchwartz ξ d

/-- The actual signed six-order coefficient of the scalar-windowed field. -/
def lowNormalQuarterWeightedSignedKernel (w : WeightV → ℝ)
    (z : WeightV × WeightV) : ℝ :=
  (Complex.I * sixOrderTriadCoefficient z.1 (middleFrequency z.1 z.2) z.2
    (lowNormalQuarterWeightedFourier w z.1)
    (lowNormalQuarterWeightedFourier w (middleFrequency z.1 z.2))
    (lowNormalQuarterWeightedFourier w z.2)).re

private theorem lowNormalScale_mixedDot (r : WeightV) (b : WeightA) (s : ℂ) :
    mixedDot r (fun d => s * b d) = s * mixedDot r b := by
  simp only [mixedDot, Fin.sum_univ_succ]
  ring

private theorem lowNormalScale_amplitudeDot (a c : WeightA) (s t : ℂ) :
    amplitudeDot (fun d => s * a d) (fun d => t * c d) =
      (s * t) * amplitudeDot a c := by
  simp only [amplitudeDot, Fin.sum_univ_succ]
  ring

private theorem lowNormalScale_complexCoefficient
    (p q r : WeightV) (b : WeightA) (s : ℂ) :
    complexCoefficient p q r (fun d => s * b d) =
      s * complexCoefficient p q r b := by
  change
    (((dot p r * (dot p q) ^ 2 : ℝ) : ℂ) *
      mixedDot r (fun d => s * b d)) =
    s * (((dot p r * (dot p q) ^ 2 : ℝ) : ℂ) * mixedDot r b)
  rw [lowNormalScale_mixedDot]
  ring

/-- Each ordered symbol is trilinear in its amplitude slots. -/
theorem lowNormalOrderedCoefficient_scale
    (p q r : WeightV) (a b c : WeightA) (s t u : ℂ) :
    orderedTriadCoefficient p q r
      (fun d => s * a d) (fun d => t * b d) (fun d => u * c d) =
      (s * t * u) * orderedTriadCoefficient p q r a b c := by
  change
    complexCoefficient p q r (fun d => t * b d) *
      amplitudeDot (fun d => s * a d) (fun d => u * c d) =
    (s * t * u) * (complexCoefficient p q r b * amplitudeDot a c)
  rw [lowNormalScale_complexCoefficient, lowNormalScale_amplitudeDot]
  ring

/-- The FULL six-permutation coefficient scales by one common triple product.
This is not merely a relation for a chosen ordered monomial. -/
theorem lowNormalSixOrderCoefficient_scale
    (p q r : WeightV) (a b c : WeightA) (s t u : ℂ) :
    sixOrderTriadCoefficient p q r
      (fun d => s * a d) (fun d => t * b d) (fun d => u * c d) =
      (s * t * u) * sixOrderTriadCoefficient p q r a b c := by
  simp only [sixOrderTriadCoefficient, lowNormalOrderedCoefficient_scale]
  ring

/-- The real signed phase is compatible with three real amplitude scalars. -/
private theorem lowNormalRealTriple_phase (s t u : ℝ) (z : ℂ) :
    (Complex.I * ((s : ℂ) * (t : ℂ) * (u : ℂ) * z)).re =
      s * t * u * (Complex.I * z).re := by
  simp [Complex.mul_re, Complex.I_re, Complex.I_im]

/-- **Exact pointwise bridge** between the original signed kernel and the
signed kernel of its scalar-windowed Fourier field. -/
theorem lowNormalQuarterWeightedSignedKernel_eq
    (w : WeightV → ℝ) (p r : WeightV) :
    lowNormalQuarterWeightedSignedKernel w (p, r) =
      w p * w (middleFrequency p r) * w r *
        lowNormalQuarterSignedKernel (p, r) := by
  change
    (Complex.I * sixOrderTriadCoefficient p (middleFrequency p r) r
      (fun d => (w p : ℂ) * lowNormalQuarterSchwartz p d)
      (fun d => (w (middleFrequency p r) : ℂ) *
        lowNormalQuarterSchwartz (middleFrequency p r) d)
      (fun d => (w r : ℂ) * lowNormalQuarterSchwartz r d)).re =
    w p * w (middleFrequency p r) * w r *
      (Complex.I * sixOrderTriadCoefficient p (middleFrequency p r) r
        (lowNormalQuarterSchwartz p)
        (lowNormalQuarterSchwartz (middleFrequency p r))
        (lowNormalQuarterSchwartz r)).re
  rw [lowNormalSixOrderCoefficient_scale]
  exact lowNormalRealTriple_phase
    (w p) (w (middleFrequency p r)) (w r) _

/-- A nonnegative window cannot turn a nonnegative reference signed kernel
into a negative one. This lemma makes the necessary sign hypotheses explicit. -/
theorem lowNormalQuarterWeightedSignedKernel_nonneg
    (w : WeightV → ℝ) (hw : ∀ ξ, 0 ≤ w ξ)
    (p r : WeightV)
    (hBase : 0 ≤ lowNormalQuarterSignedKernel (p, r)) :
    0 ≤ lowNormalQuarterWeightedSignedKernel w (p, r) := by
  rw [lowNormalQuarterWeightedSignedKernel_eq]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (hw p) (hw (middleFrequency p r))) (hw r))
    hBase

/-- Where all three window factors are strictly positive, the positive
reference signed kernel transfers strictly to the new one. -/
theorem lowNormalQuarterWeightedSignedKernel_pos
    (w : WeightV → ℝ) (p r : WeightV)
    (hp : 0 < w p)
    (hq : 0 < w (middleFrequency p r))
    (hr : 0 < w r)
    (hBase : 0 < lowNormalQuarterSignedKernel (p, r)) :
    0 < lowNormalQuarterWeightedSignedKernel w (p, r) := by
  rw [lowNormalQuarterWeightedSignedKernel_eq]
  exact mul_pos (mul_pos (mul_pos hp hq) hr) hBase

/-- If any one window factor vanishes, the actual windowed six-order signed
kernel vanishes (including all six permutations). -/
theorem lowNormalQuarterWeightedSignedKernel_zero_of_factor_zero
    (w : WeightV → ℝ) (p r : WeightV)
    (h : w p = 0 ∨ w (middleFrequency p r) = 0 ∨ w r = 0) :
    lowNormalQuarterWeightedSignedKernel w (p, r) = 0 := by
  rw [lowNormalQuarterWeightedSignedKernel_eq]
  rcases h with hp | hq | hr
  · simp [hp]
  · simp [hq]
  · simp [hr]

/-- In the already proved positive twelve-center tube, any real window
which is strictly positive at a momentum triple produces a positive
SIGNED coefficient for its own, genuinely modified Fourier field. -/
theorem lowNormalQuarterWeightedSignedKernel_pos_in_centerTube
    (w : WeightV → ℝ) (δ : ℝ)
    (hTube : ∀ z ∈ Metric.cthickening δ lowNormalQuarterCoherentCenterSet,
      (9 / 128 : ℝ) < lowNormalQuarterSignedKernel z)
    (p r : WeightV)
    (hz : (p, r) ∈ Metric.cthickening δ lowNormalQuarterCoherentCenterSet)
    (hp : 0 < w p)
    (hq : 0 < w (middleFrequency p r))
    (hr : 0 < w r) :
    0 < lowNormalQuarterWeightedSignedKernel w (p, r) := by
  exact lowNormalQuarterWeightedSignedKernel_pos w p r hp hq hr
    ((by norm_num : (0 : ℝ) < 9 / 128).trans (hTube (p, r) hz))

end
end PrimeTensor.FirstMonomialTriad
