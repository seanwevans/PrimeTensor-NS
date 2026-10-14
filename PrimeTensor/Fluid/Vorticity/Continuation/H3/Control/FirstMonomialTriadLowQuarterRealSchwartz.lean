import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterInverseCyclicBridge
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Hermitian Fourier packets reconstruct real Schwartz velocity components

The preceding module constructed complex Schwartz inverse-Fourier components
on the genuine Euclidean Hilbert carrier. We now prove the *converse*
Hermitian-to-real implication for arbitrary complex scalar Schwartz spectra.

The proof uses the actual inverse-Fourier integral, a reflection substitution
in Euclidean volume, and commutation of complex conjugation with integration.
For the explicit quarter-frequency packet, this yields THREE real Schwartz
velocity components. Complexification and Fourier transformation recover the
original spectrum exactly, including the actual divergence-free constraint.

This does NOT yet identify the `Fin 3` carrier with `Axis Depth.three` or the
canonical Point3 physical first-monomial functional.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate Topology

noncomputable section

private abbrev RealInverseE := EuclideanSpace ℝ (Fin 3)
private abbrev RealInverseV := Fin 3 → ℝ

/-- Fourier reality converse on Schwartz space: a Hermitian spectrum has a
real-valued inverse Fourier transform at EVERY physical point. -/
theorem lowNormalHermitianSchwartz_fourierInv_conj
    (F : 𝓢(RealInverseE, ℂ))
    (hHermitian : ∀ ξ : RealInverseE, F (-ξ) = star (F ξ))
    (x : RealInverseE) :
    star ((𝓕⁻ F) x) = (𝓕⁻ F) x := by
  have hInv : (𝓕⁻ F) x = 𝓕⁻ (F : RealInverseE → ℂ) x :=
    congrFun (SchwartzMap.fourierInv_coe F) x
  simp only [hInv, Complex.star_def, Real.fourierInv_eq]
  rw [← integral_conj]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with ξ
  change star ((𝐞 (inner ℝ (-ξ) x) : ℂ) * F (-ξ)) =
    (𝐞 (inner ℝ ξ x) : ℂ) * F ξ
  rw [hHermitian ξ, star_mul', star_star, Circle.star_addChar]
  simp only [inner_neg_left, neg_neg]

/-- A pointwise Hermitian Schwartz frequency component has a real-valued
inverse Fourier transform, not just almost-everywhere reality. -/
theorem lowNormalHermitianSchwartz_fourierInv_im_zero
    (F : 𝓢(RealInverseE, ℂ))
    (hHermitian : ∀ ξ : RealInverseE, F (-ξ) = star (F ξ))
    (x : RealInverseE) :
    ((𝓕⁻ F) x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [Complex.star_def] using
    lowNormalHermitianSchwartz_fourierInv_conj F hHermitian x

/-- Hermitian property of ONE Hilbert-carrier frequency component of the
actual noncancelling quarter packet. -/
theorem lowNormalQuarterHilbertFourierComponent_hermitian
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) (ξ : RealInverseE) :
    lowNormalQuarterHilbertFourierComponent ρ hρ j (-ξ) =
      star (lowNormalQuarterHilbertFourierComponent ρ hρ j ξ) := by
  simp only [lowNormalQuarterHilbertFourierComponent_apply, WithLp.ofLp_neg]
  exact congrFun
    (lowNormalQuarterWindowedFourier_reality ρ hρ (WithLp.ofLp ξ)) j

/-- The inverse-Fourier construction from the previous commit is real at
EVERY point, not merely almost everywhere. -/
theorem lowNormalQuarterInverseSchwartz_im_zero
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) (x : RealInverseE) :
    (lowNormalQuarterInverseSchwartzComponent ρ hρ j x).im = 0 := by
  exact lowNormalHermitianSchwartz_fourierInv_im_zero
    (lowNormalQuarterHilbertFourierComponent ρ hρ j)
    (lowNormalQuarterHilbertFourierComponent_hermitian ρ hρ j) x

/-- The ACTUAL spatial velocity component, now as a real Schwartz map. -/
noncomputable def lowNormalQuarterRealSchwartzComponent
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) : 𝓢(RealInverseE, ℝ) :=
  (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM)
    (lowNormalQuarterInverseSchwartzComponent ρ hρ j)

@[simp] theorem lowNormalQuarterRealSchwartzComponent_apply
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) (x : RealInverseE) :
    lowNormalQuarterRealSchwartzComponent ρ hρ j x =
      (lowNormalQuarterInverseSchwartzComponent ρ hρ j x).re := rfl

/-- Complexifying the real Schwartz reconstruction gives the originally
inverted complex Schwartz function EXACTLY (as Schwartz maps). -/
theorem lowNormalQuarterRealSchwartz_complexify_eq_inverse
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) :
    (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM)
      (lowNormalQuarterRealSchwartzComponent ρ hρ j) =
        lowNormalQuarterInverseSchwartzComponent ρ hρ j := by
  ext x
  change (((lowNormalQuarterInverseSchwartzComponent ρ hρ j x).re : ℝ) : ℂ) =
    lowNormalQuarterInverseSchwartzComponent ρ hρ j x
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im]
    exact (lowNormalQuarterInverseSchwartz_im_zero ρ hρ j x).symm

/-- Fourier transforming the complexification of the REAL velocity component
recovers the original prescribed Hilbert-frequency Schwartz packet. -/
theorem lowNormalQuarterRealSchwartz_fourier_component
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) :
    𝓕 ((SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM)
        (lowNormalQuarterRealSchwartzComponent ρ hρ j)) =
      lowNormalQuarterHilbertFourierComponent ρ hρ j := by
  rw [lowNormalQuarterRealSchwartz_complexify_eq_inverse]
  exact lowNormalQuarterInverseSchwartz_fourier_component ρ hρ j

/-- The recovered Fourier vector of the REAL spatial Schwartz velocity is
exactly the original noncancelling weighted Fourier field. -/
theorem lowNormalQuarterRealSchwartz_fourier_vector
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : RealInverseE) :
    (fun j : Fin 3 =>
      𝓕 ((SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM)
        (lowNormalQuarterRealSchwartzComponent ρ hρ j)) ξ) =
      lowNormalQuarterWeightedFourier
        (lowNormalQuarterEvenWindow ρ hρ) (WithLp.ofLp ξ) := by
  funext j
  rw [lowNormalQuarterRealSchwartz_fourier_component]
  exact lowNormalQuarterHilbertFourierComponent_apply ρ hρ j ξ

/-- Its original pointwise Fourier incompressibility survives REAL spatial
reconstruction, with no extra hypotheses. -/
theorem lowNormalQuarterRealSchwartz_fourier_divergence
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : RealInverseE) :
    mixedDot (WithLp.ofLp ξ)
      (fun j : Fin 3 =>
        𝓕 ((SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM)
          (lowNormalQuarterRealSchwartzComponent ρ hρ j)) ξ) = 0 := by
  rw [lowNormalQuarterRealSchwartz_fourier_vector]
  exact lowNormalQuarterWindowedFourier_divergence ρ hρ (WithLp.ofLp ξ)

end
end PrimeTensor.FirstMonomialTriad
