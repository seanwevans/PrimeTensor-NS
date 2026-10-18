import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealDensityIntegral244
import Mathlib.Tactic

/-!
# Remove the seventh-order phase from the full real H3 transport coefficient

The complete real physical third commutator has been identified with the
integral of an absolutely integrable, reflection-even signed Fourier density.
The factor `(2 * pi * I)^7` is common to all four 3+3+1 gradient channels and
the 3+2+2 interpolation channel. We remove this common purely imaginary
phase without changing any physical coefficients or swapping any frequencies.

The resulting UNPHASED kernel is an actual trilinear expression in the
recovered Fourier transforms of our real solenoidal Schwartz velocity, with
all five physical axis sums. The physical commutator is exactly
`(2*pi)^7` times the integral of its imaginary part. The positive scalar
factor makes signed noncancellation an equivalent, phase-free problem.

This does NOT prove that the kernel has a constant sign on the six positive
coherent sectors. It isolates that remaining mathematical obligation.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform Topology

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev V3 := H3FourierPoint3
private abbrev PairV244 := V3 × V3

noncomputable local instance axisFintypeImaginary244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- All four genuine 3+3+1 physical gradient slots, with the energy factor 2
but without the shared seventh-derivative Fourier phase. -/
noncomputable def thirdFullAxisRealGradientAxisUnphased244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j i k l r : A3) (z : PairV244) : ℂ :=
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  2 * (((thirdFullAxisRealGradientSlot244 ρ hρ A B C
           j r j a b c a b c d z +
         thirdFullAxisRealGradientSlot244 ρ hρ A B C
           j j r a b c a b d c z) +
         thirdFullAxisRealGradientSlot244 ρ hρ A B C
           j j r a b c a d c b z) +
         thirdFullAxisRealGradientSlot244 ρ hρ A B C
           j j r a b c d b c a z)

/-- Remove the phase at one fixed ordered five-index gradient label. -/
theorem thirdFullAxisRealGradientAxisComplexDensity_eq_phase_unphased244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j i k l r : A3)
    (z : PairV244) :
    thirdFullAxisRealGradientAxisComplexDensity244 ρ hρ A B C j i k l r z =
      (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        thirdFullAxisRealGradientAxisUnphased244 ρ hρ A B C j i k l r z := by
  unfold thirdFullAxisRealGradientAxisComplexDensity244
    thirdFullAxisRealGradientAxisUnphased244
  ring

/-- Preserve the FIVE finite physical axis sums, before any analytic step. -/
noncomputable def thirdFullAxisRealGradientTotalUnphased244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) : ℂ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
    thirdFullAxisRealGradientAxisUnphased244 ρ hρ A B C j i k l r z

/-- The Fourier phase factors out of every one of the five index sums. -/
theorem thirdFullAxisRealGradientTotalComplexDensity_eq_phase_unphased244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) :
    thirdFullAxisRealGradientTotalComplexDensity244 ρ hρ A B C z =
      (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        thirdFullAxisRealGradientTotalUnphased244 ρ hρ A B C z := by
  unfold thirdFullAxisRealGradientTotalComplexDensity244
    thirdFullAxisRealGradientTotalUnphased244
  simp_rw [thirdFullAxisRealGradientAxisComplexDensity_eq_phase_unphased244]
  simp only [Finset.mul_sum]

/-- ONE unphased trilinear kernel for the entire H3 third commutator:
2 times all four gradient patterns and 6 times the true interpolation kernel. -/
noncomputable def thirdFullAxisRealThirdUnphasedKernel244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) : ℂ :=
  thirdFullAxisRealGradientTotalUnphased244 ρ hρ A B C z +
    6 * thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z

/-- No phase factor is lost or sign-flipped in either physical channel. -/
theorem thirdFullAxisRealThirdComplexDensity_eq_phase_unphased244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) :
    thirdFullAxisRealThirdComplexDensity244 ρ hρ A B C z =
      (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z := by
  unfold thirdFullAxisRealThirdComplexDensity244
    thirdFullAxisRealThirdUnphasedKernel244
  rw [thirdFullAxisRealGradientTotalComplexDensity_eq_phase_unphased244]
  ring

/-- Every unphased gradient block is absolutely integrable, since all four
literal recovered-Schwartz Fourier slots are absolutely integrable. -/
theorem thirdFullAxisRealGradientAxisUnphased_integrable244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j i k l r : A3) :
    Integrable (thirdFullAxisRealGradientAxisUnphased244
      ρ hρ A B C j i k l r) (volume.prod volume) := by
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  have h1 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j r j a b c a b c d
  have h2 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j j r a b c a b d c
  have h3 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j j r a b c a d c b
  have h4 := thirdFullAxisRealGradientSlot_integrable244
    ρ hρ A B C j j r a b c d b c a
  exact (((h1.add h2).add h3).add h4).const_mul (2 : ℂ)

/-- Unphased full gradient summation is absolutely integrable. -/
theorem thirdFullAxisRealGradientTotalUnphased_integrable244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    Integrable (thirdFullAxisRealGradientTotalUnphased244 ρ hρ A B C)
      (volume.prod volume) := by
  unfold thirdFullAxisRealGradientTotalUnphased244
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro l _
  apply integrable_finsetSum
  intro r _
  exact thirdFullAxisRealGradientAxisUnphased_integrable244
    ρ hρ A B C j i k l r

/-- Absolute convergence is retained when removing the nonzero common phase. -/
theorem thirdFullAxisRealThirdUnphasedKernel_integrable244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    Integrable (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C)
      (volume.prod volume) := by
  exact (thirdFullAxisRealGradientTotalUnphased_integrable244
    ρ hρ A B C).add
      ((thirdFullAxisRealInterpolationKernel_integrable244 ρ hρ A B C).const_mul
        (6 : ℂ))

/-- The ODD seventh derivative phase converts exactly to the imaginary part
of its unphased Fourier kernel, with a positive real normalization. -/
theorem thirdFullSeventhPhase_real_eq_imag244 (w : ℂ) :
    (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) * w).re =
      (2 * Real.pi) ^ 7 * w.im := by
  rw [h3FirstMonomial_fourier_phase]
  -- First expose the real part of the product with the seventh-order phase.
  -- Simplification of the real power leaves an *inner* complex imaginary
  -- part, which needs a second normalization pass before ring can close.
  simp only [Complex.neg_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, zero_sub, one_mul, neg_zero]
  simp only [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, zero_add, one_mul]
  ring

/-- The actual COMPLETE signed real Fourier density is exactly a POSITIVE
scalar multiple of the imaginary part of one unphased trilinear kernel. -/
theorem thirdFullAxisRealThirdSignedDensity_eq_imagKernel244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) :
    thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C z =
      (2 * Real.pi) ^ 7 *
        (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im := by
  rw [thirdFullAxisRealThirdSignedDensity_eq_complex_re244,
    thirdFullAxisRealThirdComplexDensity_eq_phase_unphased244]
  exact thirdFullSeventhPhase_real_eq_imag244 _

/-- The IMAGINARY unphased kernel is even under Hermitian reflection. This
follows from actual physical density parity and strict phase positivity,
not from an unsupported assertion about the twelve-sector values. -/
theorem thirdFullAxisRealThirdUnphasedImag_reflect244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) :
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C (-z.1, -z.2)).im =
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im := by
  have h := thirdFullAxisRealThirdSignedDensity_reflect244 ρ hρ A B C z
  simp only [thirdFullAxisRealThirdSignedDensity_eq_imagKernel244] at h
  have hc : (2 * Real.pi) ^ 7 ≠ (0 : ℝ) :=
    ne_of_gt (pow_pos (mul_pos (by norm_num) Real.pi_pos) 7)
  exact (mul_left_cancel₀ hc) h

/-- The unphased IMAGINARY physical kernel has no mass outside the
TWELVE-center coherent Fourier tube, even though its full complex value need
not have a fixed sign. -/
theorem thirdFullAxisRealThirdUnphasedImag_zero_off_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244)
    (z : PairV244)
    (hz : z ∉ thirdFullAxisRealHilbertCoherentTube244 δ) :
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im = 0 := by
  have h := thirdFullAxisRealThirdSignedDensity_zero_off_tube244
    ρ hρ hSmall δ hρδ A B C z hz
  rw [thirdFullAxisRealThirdSignedDensity_eq_imagKernel244] at h
  have hc : (2 * Real.pi) ^ 7 ≠ (0 : ℝ) :=
    ne_of_gt (pow_pos (mul_pos (by norm_num) Real.pi_pos) 7)
  exact (mul_eq_zero.mp h).resolve_left hc

/-- EXACT original real physical commutator = positive Fourier normalization
 times the full integral of the unphased imaginary kernel. -/
theorem thirdFullAxisRealThirdCommutator_eq_imagKernel_integral244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
    (2 * Real.pi) ^ 7 *
      ∫ z : PairV244,
        (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume := by
  rw [thirdFullAxisRealThirdCommutator_eq_signedDensity_integral244]
  calc
    (∫ z : PairV244,
        thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C z
        ∂volume.prod volume) =
      ∫ z : PairV244,
        (2 * Real.pi) ^ 7 *
          (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume := by
          apply integral_congr_ae
          filter_upwards with z
          exact thirdFullAxisRealThirdSignedDensity_eq_imagKernel244
            ρ hρ A B C z
    _ = _ := integral_const_mul _ _

/-- The phase-free physical integral also admits the SAME exact twelve-sector
indicator restriction as the original complete signed density. -/
theorem thirdFullAxisRealThirdCommutator_eq_imagKernel_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244) :
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
    (2 * Real.pi) ^ 7 *
      ∫ z : PairV244,
        (thirdFullAxisRealHilbertCoherentTube244 δ).indicator
          (fun z => (thirdFullAxisRealThirdUnphasedKernel244
            ρ hρ A B C z).im) z
        ∂volume.prod volume := by
  rw [thirdFullAxisRealThirdCommutator_eq_imagKernel_integral244]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  classical
  change (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im =
    if z ∈ thirdFullAxisRealHilbertCoherentTube244 δ then
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im else 0
  split_ifs with hz
  · rfl
  · exact thirdFullAxisRealThirdUnphasedImag_zero_off_tube244
      ρ hρ hSmall δ hρδ A B C z hz

/-- The remaining NONCANCELLATION problem is exactly the sign of the
unphased imaginary Fourier integral; the factor `(2*pi)^7` cannot change it. -/
theorem thirdFullAxisRealThirdCommutator_neg_iff_imagKernel_integral_neg244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    fullSchwartzThirdCommutator244
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) < 0 ↔
      (∫ z : PairV244,
        (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume) < 0 := by
  rw [thirdFullAxisRealThirdCommutator_eq_imagKernel_integral244]
  have hc : 0 < (2 * Real.pi) ^ 7 :=
    pow_pos (mul_pos (by norm_num) Real.pi_pos) 7
  constructor
  · intro h
    by_contra hn
    have hNonneg : 0 ≤ (∫ z : PairV244,
        (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume) := le_of_not_gt hn
    exact (not_lt_of_ge (mul_nonneg hc.le hNonneg)) h
  · intro h
    exact mul_neg_of_pos_of_neg hc h

end
end PrimeTensor.FirstMonomialTriad
