import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealGradientHermitianReflection244
import Mathlib.Tactic

/-!
# Hermitian reflection of the actual full-third interpolation and signed density

The complete physical H3 commutator is already identified with exact Fourier
integrals of 3+3+1 gradient slots and the 3+2+2 interpolation kernel of the
constructed REAL divergence-free Schwartz velocity. The gradient slots were
proved odd-conjugate under momentum-pair reflection.

Here we prove the corresponding result for the *actual* interpolation kernel,
using the finite-index bilinear amplitude contraction rather than an invented
symbol. Both channels therefore have even seven-derivative signed densities.
We assemble the full physical index sum as a pointwise real signed density.

This reflection identity is an exact pointwise statement. It does not prove
that the full signed integral is nonzero or that every sector has one sign.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Topology

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev Pair244 := Freq244 × Freq244
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdInterpReflect244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Simultaneously negating two real frequency vectors preserves their dot. -/
private theorem thirdFullReflect_dot244 (p r : Freq244) :
    dot (-p) (-r) = dot p r := by
  simp [dot, Pi.neg_apply]

/-- One frequency/polarization contraction is odd-conjugate under reflection. -/
private theorem thirdFullReflect_mixedDot244
    (p : Freq244) (b : A3 → ℂ) :
    mixedDot (-p) (fun j => star (b j)) =
      -star (mixedDot p b) := by
  change mixedDot (-p) (fun j => (starRingEnd ℂ) (b j)) =
    -(starRingEnd ℂ) (mixedDot p b)
  simp [mixedDot, Pi.neg_apply, map_sum, map_mul, Complex.conj_ofReal]

/-- Bilinear outer-frequency contraction respects complex conjugation. -/
private theorem thirdFullReflect_amplitudeDot244
    (a c : A3 → ℂ) :
    amplitudeDot (fun j => star (a j)) (fun j => star (c j)) =
      star (amplitudeDot a c) := by
  change amplitudeDot (fun j => (starRingEnd ℂ) (a j))
      (fun j => (starRingEnd ℂ) (c j)) =
    (starRingEnd ℂ) (amplitudeDot a c)
  simp [amplitudeDot, map_sum, map_mul]

/-- The actual scalar interpolation coefficient is odd-conjugate. -/
private theorem thirdFullReflect_complexCoefficient244
    (p q r : Freq244) (b : A3 → ℂ) :
    complexCoefficient (-p) (-q) (-r) (fun j => star (b j)) =
      -star (complexCoefficient p q r b) := by
  unfold complexCoefficient
  rw [thirdFullReflect_dot244 p r, thirdFullReflect_dot244 p q,
    thirdFullReflect_mixedDot244 r b]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

/-- The dependent middle momentum reflects together with both outer momenta. -/
private theorem thirdFullReflect_middle244 (p r : Freq244) :
    middleFrequency (-p) (-r) = -(middleFrequency p r) := by
  funext j
  simp [middleFrequency, Pi.neg_apply]
  ring

/-- General cubic interpolation amplitude parity for any Hermitian spectrum. -/
theorem thirdFullAxisAmplitudeKernel_reflect244
    (U : Freq244 → A3 → ℂ)
    (hU : ∀ ξ : Freq244, U (-ξ) = fun j => star (U ξ j))
    (z : Pair244) :
    amplitudeKernel U (-z.1, -z.2) =
      -star (amplitudeKernel U z) := by
  rcases z with ⟨p, r⟩
  change complexCoefficient (-p) (middleFrequency (-p) (-r)) (-r)
      (U (middleFrequency (-p) (-r))) * amplitudeDot (U (-p)) (U (-r)) =
    -star (complexCoefficient p (middleFrequency p r) r
      (U (middleFrequency p r)) * amplitudeDot (U p) (U r))
  rw [thirdFullReflect_middle244 p r,
    hU (middleFrequency p r), hU p, hU r,
    thirdFullReflect_complexCoefficient244,
    thirdFullReflect_amplitudeDot244]
  simp only [star_mul', neg_mul]

/-- The ACTUAL 3+2+2 Schwartz Fourier kernel of the recovered real packet
obeys the same odd-conjugate rule as every physical 3+3+1 gradient slot. -/
theorem thirdFullAxisRealInterpolationKernel_reflect244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : V3 × V3) :
    thirdFullAxisRealInterpolationKernel244 ρ hρ A B C (-z.1, -z.2) =
      -star (thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z) := by
  rw [thirdFullAxisRealInterpolationKernel_eq_amplitude244,
    thirdFullAxisRealInterpolationKernel_eq_amplitude244]
  simpa only [WithLp.ofLp_neg] using
    (thirdFullAxisAmplitudeKernel_reflect244
      (thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C)
      (thirdFullAxisRealSpectrum_reflect244 ρ hρ A B C)
      (WithLp.ofLp z.1, WithLp.ofLp z.2))

/-- The interpolation channel's seven-derivative signed REAL density is
pointwise even under frequency-pair reflection. -/
theorem thirdFullAxisRealInterpolationKernel_signed_reflect244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : V3 × V3) :
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      thirdFullAxisRealInterpolationKernel244 ρ hρ A B C (-z.1, -z.2)).re =
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z).re := by
  rw [thirdFullAxisRealInterpolationKernel_reflect244]
  exact thirdFullSeventhPhase_oddConj_re244 _

/-- All FOUR genuine signed 3+3+1 gradient slots at one ordered physical
five-index position, including the energy-pairing coefficient two. -/
noncomputable def thirdFullAxisRealGradientAxisSignedDensity244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j i k l r : A3) (z : V3 × V3) : ℝ :=
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  let phase := (2 * (Real.pi : ℂ) * Complex.I) ^ 7
  2 * (
    (phase * thirdFullAxisRealGradientSlot244 ρ hρ A B C
      j r j a b c a b c d z).re +
    (phase * thirdFullAxisRealGradientSlot244 ρ hρ A B C
      j j r a b c a b d c z).re +
    (phase * thirdFullAxisRealGradientSlot244 ρ hρ A B C
      j j r a b c a d c b z).re +
    (phase * thirdFullAxisRealGradientSlot244 ρ hρ A B C
      j j r a b c d b c a z).re)

/-- The entire four-pattern signed gradient block is even at every point. -/
theorem thirdFullAxisRealGradientAxisSignedDensity_reflect244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j i k l r : A3) (z : V3 × V3) :
    thirdFullAxisRealGradientAxisSignedDensity244
      ρ hρ A B C j i k l r (-z.1, -z.2) =
    thirdFullAxisRealGradientAxisSignedDensity244
      ρ hρ A B C j i k l r z := by
  simp only [thirdFullAxisRealGradientAxisSignedDensity244,
    thirdFullAxisRealGradientSlot_signed_reflect244]

/-- The genuine four-pattern real gradient density is zero outside the
coherent tube, without using any sign argument. -/
theorem thirdFullAxisRealGradientAxisSignedDensity_zero_off_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244)
    (j i k l r : A3) (z : V3 × V3)
    (hz : z ∉ thirdFullAxisRealHilbertCoherentTube244 δ) :
    thirdFullAxisRealGradientAxisSignedDensity244
      ρ hρ A B C j i k l r z = 0 := by
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  have h1 := thirdFullAxisRealGradientSlot_zero_off_coherent_tube244
    ρ hρ hSmall δ hρδ A B C j r j a b c a b c d z hz
  have h2 := thirdFullAxisRealGradientSlot_zero_off_coherent_tube244
    ρ hρ hSmall δ hρδ A B C j j r a b c a b d c z hz
  have h3 := thirdFullAxisRealGradientSlot_zero_off_coherent_tube244
    ρ hρ hSmall δ hρδ A B C j j r a b c a d c b z hz
  have h4 := thirdFullAxisRealGradientSlot_zero_off_coherent_tube244
    ρ hρ hSmall δ hρδ A B C j j r a b c d b c a z hz
  -- Reduce just the outer density definition, not `Complex.mul_re`.
  -- The latter destroys the syntactic slot terms before h1--h4 can rewrite.
  change (2 : ℝ) * (
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      thirdFullAxisRealGradientSlot244 ρ hρ A B C
        j r j a b c a b c d z).re +
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      thirdFullAxisRealGradientSlot244 ρ hρ A B C
        j j r a b c a b d c z).re +
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      thirdFullAxisRealGradientSlot244 ρ hρ A B C
        j j r a b c a d c b z).re +
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      thirdFullAxisRealGradientSlot244 ρ hρ A B C
        j j r a b c d b c a z).re) = 0
  rw [h1, h2, h3, h4]
  simp

/-- Complete signed REAL density: all five coordinate sums and four genuine
3+3+1 gradient terms, plus six times the true 3+2+2 interpolation kernel.
This definition does NOT replace the exact physical integral identity. -/
noncomputable def thirdFullAxisRealThirdSignedDensity244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : V3 × V3) : ℝ :=
  (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
    thirdFullAxisRealGradientAxisSignedDensity244
      ρ hρ A B C j i k l r z) +
  6 * (((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
    thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z).re)

/-- **Complete physical seven-derivative pointwise parity.** Neither the
reflected sectors nor the original sectors can cancel *merely because* of
simultaneous Hermitian reflection. The remaining global signed summation is
not evaluated by this theorem. -/
theorem thirdFullAxisRealThirdSignedDensity_reflect244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : V3 × V3) :
    thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C (-z.1, -z.2) =
      thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C z := by
  simp only [thirdFullAxisRealThirdSignedDensity244,
    thirdFullAxisRealGradientAxisSignedDensity_reflect244,
    thirdFullAxisRealInterpolationKernel_signed_reflect244]

/-- The COMPLETE signed real third-order density inherits the same exact
support as the true Fourier amplitudes of the recovered Schwartz velocity. -/
theorem thirdFullAxisRealThirdSignedDensity_zero_off_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244)
    (z : V3 × V3)
    (hz : z ∉ thirdFullAxisRealHilbertCoherentTube244 δ) :
    thirdFullAxisRealThirdSignedDensity244 ρ hρ A B C z = 0 := by
  have hG (j i k l r : A3) :
      thirdFullAxisRealGradientAxisSignedDensity244
        ρ hρ A B C j i k l r z = 0 :=
    thirdFullAxisRealGradientAxisSignedDensity_zero_off_tube244
      ρ hρ hSmall δ hρδ A B C j i k l r z hz
  have hI := thirdFullAxisRealInterpolationKernel_zero_off_tube244
    ρ hρ hSmall δ hρδ A B C z hz
  simp [thirdFullAxisRealThirdSignedDensity244, hG, hI]

end
end PrimeTensor.FirstMonomialTriad
