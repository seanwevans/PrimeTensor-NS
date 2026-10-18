import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealGradientMultiplier244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealFourierIdentification244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Exact coherent-tube integral for the complete real full-third commutator

The constructed real, divergence-free full-third Schwartz velocity has six
compact Hermitian Fourier windows and an exact frequency-space realization.
Previous work localizes each genuine seven-derivative 3+3+1 gradient Fourier
slot to the twelve coherent momentum sectors. Here we aggregate ALL FOUR
ordered gradient slots and all FIVE physical coordinate sums without changing
the factor two or the Fourier phase. We also prove that the separate 3+2+2
Schwartz interpolation kernel vanishes outside the same coherent tube.

Combining these identities gives an exact coherent-tube Fourier integral
representation of the COMPLETE static H3 commutator of the actual REAL field.
This is a localization identity, NOT a global sign/noncancellation result:
the twelve coherent contributions could still cancel after integration.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform Topology

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev Pair244 := Freq244 × Freq244
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullCoefficientTube244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The common twelve-sector tube pulled back to the physical Euclidean
Fourier pair carrier. The explicit preimage avoids a hidden Jacobian. -/
def thirdFullAxisRealHilbertCoherentTube244 (δ : ℝ) : Set (V3 × V3) :=
  {z | (WithLp.ofLp z.1, WithLp.ofLp z.2) ∈
    Metric.cthickening δ thirdFullAxisCoherentPairCenterSet244}

/-- The SAME four Fourier integrals in the actual physical gradient block,
now restricted to the one coherent tube. The exact physical factor 2 and
the full seven-derivative Fourier phase are retained. -/
noncomputable def thirdFullAxisRealGradientAxisTube244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (δ : ℝ)
    (j i k l r : A3) : ℂ :=
  let T := thirdFullAxisRealHilbertCoherentTube244 δ
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
    ((∫ z : V3 × V3,
        T.indicator (thirdFullAxisRealGradientSlot244 ρ hρ A B C
          j r j a b c a b c d) z ∂volume.prod volume) +
     (∫ z : V3 × V3,
        T.indicator (thirdFullAxisRealGradientSlot244 ρ hρ A B C
          j j r a b c a b d c) z ∂volume.prod volume) +
     (∫ z : V3 × V3,
        T.indicator (thirdFullAxisRealGradientSlot244 ρ hρ A B C
          j j r a b c a d c b) z ∂volume.prod volume) +
     (∫ z : V3 × V3,
        T.indicator (thirdFullAxisRealGradientSlot244 ρ hρ A B C
          j j r a b c d b c a) z ∂volume.prod volume))

/-- Each complete FOUR-pattern physical gradient block equals its twelve-
sector tube expression; the argument uses the four actual Fourier-slot
integral theorems, not an abstract polynomial approximation. -/
theorem thirdFullAxisRealGradientAxis_eq_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244)
    (j i k l r : A3) :
    thirdGradientSchwartzAxisFourier244
        (fun t => h3SchwartzComplexify
          (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C t))
        j i k l r =
      thirdFullAxisRealGradientAxisTube244 ρ hρ A B C δ j i k l r := by
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  have h1 := thirdFullAxisRealGradientSlot_integral_eq_coherent_tube244
    ρ hρ hSmall δ hρδ A B C j r j a b c a b c d
  have h2 := thirdFullAxisRealGradientSlot_integral_eq_coherent_tube244
    ρ hρ hSmall δ hρδ A B C j j r a b c a b d c
  have h3 := thirdFullAxisRealGradientSlot_integral_eq_coherent_tube244
    ρ hρ hSmall δ hρδ A B C j j r a b c a d c b
  have h4 := thirdFullAxisRealGradientSlot_integral_eq_coherent_tube244
    ρ hρ hSmall δ hρδ A B C j j r a b c d b c a
  -- Rewrite the four indicator integrals back to their actual Fourier slots.
  unfold thirdFullAxisRealGradientAxisTube244
  simp only [thirdFullAxisRealHilbertCoherentTube244] at h1 h2 h3 h4 ⊢
  rw [← h1, ← h2, ← h3, ← h4]
  rfl

/-- All five axis sums of the actual 3+3+1 gradient transport have been
localized to the coherent sectors. -/
noncomputable def thirdFullAxisRealGradientTotalTube244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (δ : ℝ) : ℂ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
    thirdFullAxisRealGradientAxisTube244 ρ hρ A B C δ j i k l r

theorem thirdFullAxisRealGradientTotal_eq_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244) :
    thirdGradientFourierTotalComplex244
        (fun t => h3SchwartzComplexify
          (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C t)) =
      thirdFullAxisRealGradientTotalTube244 ρ hρ A B C δ := by
  unfold thirdGradientFourierTotalComplex244
    thirdFullAxisRealGradientTotalTube244
  simp_rw [thirdFullAxisRealGradientAxis_eq_tube244 ρ hρ hSmall δ hρδ A B C]

/-- The TRUE 3+2+2 interpolation Fourier kernel of the same real Schwartz
velocity. In particular, it is the existing project's actual first-monomial
triad kernel, not a new ansatz. -/
noncomputable def thirdFullAxisRealInterpolationKernel244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : V3 × V3) : ℂ :=
  h3SchwartzTriadKernel
    (fun j => h3SchwartzComplexify
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C j)) z

/-- The interpolation kernel is exactly the coordinate-space amplitude
kernel built from the recovered full-third Fourier spectrum. -/
theorem thirdFullAxisRealInterpolationKernel_eq_amplitude244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : V3 × V3) :
    thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z =
      amplitudeKernel (thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C)
        (WithLp.ofLp z.1, WithLp.ofLp z.2) := rfl

/-- The genuine 3+2+2 interpolation integrand vanishes whenever any of
its THREE frequency amplitudes vanishes. The coefficient is still the
literal physical Schwartz amplitude kernel. -/
theorem thirdFullAxisRealInterpolationKernel_zero_of_mass244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : V3 × V3)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) = 0) :
    thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z = 0 := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let U := thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
  rw [thirdFullAxisRealInterpolationKernel_eq_amplitude244]
  change complexCoefficient p q r (U q) * amplitudeDot (U p) (U r) = 0
  by_cases hp : U p = 0
  · simp [amplitudeDot, hp]
  by_cases hq : U q = 0
  · simp [complexCoefficient, mixedDot, hq]
  by_cases hr : U r = 0
  · simp [amplitudeDot, hr]
  have hp' : ‖U p‖ ≠ 0 := by
    intro h; exact hp (norm_eq_zero.mp h)
  have hq' : ‖U q‖ ≠ 0 := by
    intro h; exact hq (norm_eq_zero.mp h)
  have hr' : ‖U r‖ ≠ 0 := by
    intro h; exact hr (norm_eq_zero.mp h)
  have hNonzero : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (p, r) ≠ 0 := by
    change ‖U p‖ * ‖U q‖ * ‖U r‖ ≠ 0
    exact mul_ne_zero (mul_ne_zero hp' hq') hr'
  exact (hNonzero hMass).elim

/-- The 3+2+2 actual interpolation kernel has precisely the same frequency
support exclusion as the already verified 3+3+1 gradient kernel. -/
theorem thirdFullAxisRealInterpolationKernel_zero_off_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244)
    (z : V3 × V3)
    (hz : z ∉ thirdFullAxisRealHilbertCoherentTube244 δ) :
    thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z = 0 := by
  let p := WithLp.ofLp z.1
  let r := WithLp.ofLp z.2
  have hAway : (p, r) ∉
      Metric.thickening ρ thirdFullAxisCoherentPairCenterSet244 := by
    intro hNear
    exact hz ((Metric.thickening_subset_cthickening_of_le hρδ
      thirdFullAxisCoherentPairCenterSet244) hNear)
  have hMass := thirdFullAxisRealSchwartzTripleMass_zero_off_tube244
    ρ hρ hSmall A B C (p, r) hAway
  exact thirdFullAxisRealInterpolationKernel_zero_of_mass244
    ρ hρ A B C z hMass

/-- Absolute integrability is inherited from the preexisting exact 3+2+2
Schwartz Fourier theorem. -/
theorem thirdFullAxisRealInterpolationKernel_integrable244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    Integrable (thirdFullAxisRealInterpolationKernel244 ρ hρ A B C)
      (volume.prod volume) := by
  exact h3SchwartzTriadKernel_integrable _

/-- Exact equality of the full 3+2+2 interpolation integral to its restriction
to the SAME physical Hilbert-carrier coherent tube as the gradient slots. -/
theorem thirdFullAxisRealInterpolationKernel_integral_eq_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244) :
    (∫ z : V3 × V3, thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z
      ∂volume.prod volume) =
    ∫ z : V3 × V3,
      (thirdFullAxisRealHilbertCoherentTube244 δ).indicator
        (thirdFullAxisRealInterpolationKernel244 ρ hρ A B C) z
      ∂volume.prod volume := by
  classical
  apply integral_congr_ae
  filter_upwards with z
  change thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z =
    if z ∈ thirdFullAxisRealHilbertCoherentTube244 δ then
      thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z else 0
  split_ifs with hz
  · rfl
  · exact thirdFullAxisRealInterpolationKernel_zero_off_tube244
      ρ hρ hSmall δ hρδ A B C z hz

/-- COMPLETE complex coefficient: all four physical 3+3+1 gradient slots,
all five original axis sums, plus the exact 3+2+2 interpolation coefficient
6 = 3 (interpolation multiplicity) times 2 (energy pairing).
No assertion about sign or noncancellation is made here. -/
noncomputable def thirdFullAxisRealFullCoefficientTube244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (δ : ℝ) : ℂ :=
  thirdFullAxisRealGradientTotalTube244 ρ hρ A B C δ +
    6 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      ∫ z : V3 × V3,
        (thirdFullAxisRealHilbertCoherentTube244 δ).indicator
          (thirdFullAxisRealInterpolationKernel244 ρ hρ A B C) z
          ∂volume.prod volume

/-- The actual full-third physical Fourier coefficient equals its exact
coherent-tube expression. All original coefficients remain unchanged. -/
theorem thirdFullAxisRealFullCoefficient_eq_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244) :
    fullThirdSchwartzFourierCoefficient244
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
      thirdFullAxisRealFullCoefficientTube244 ρ hρ A B C δ := by
  change
    thirdGradientFourierTotalComplex244
      (fun j => h3SchwartzComplexify
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C j)) +
    6 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      (∫ z : V3 × V3,
        thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z
        ∂volume.prod volume) =
      thirdFullAxisRealGradientTotalTube244 ρ hρ A B C δ +
    6 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      (∫ z : V3 × V3,
        (thirdFullAxisRealHilbertCoherentTube244 δ).indicator
          (thirdFullAxisRealInterpolationKernel244 ρ hρ A B C) z
          ∂volume.prod volume)
  rw [thirdFullAxisRealGradientTotal_eq_tube244
      ρ hρ hSmall δ hρδ A B C,
    thirdFullAxisRealInterpolationKernel_integral_eq_tube244
      ρ hρ hSmall δ hρδ A B C]

/-- The physical static H3 third commutator of our REAL divergence-free
Schwartz velocity is the real part of a COMPLETE localized Fourier
coefficient. The total signed integral is not yet evaluated. -/
theorem thirdFullAxisRealThirdCommutator_eq_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (A B C : Freq244) :
    fullSchwartzThirdCommutator244
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
      (thirdFullAxisRealFullCoefficientTube244 ρ hρ A B C δ).re := by
  rw [thirdFullAxisRealSchwartz_commutator_eq_fourier244]
  rw [thirdFullAxisRealFullCoefficient_eq_tube244
    ρ hρ hSmall δ hρδ A B C]

/-- Uniform choice of a small positive Fourier-packet width: for EVERY
prescribed positive coherent-tube radius and ALL real polarization parameters,
the COMPLETE physical seven-derivative static commutator has this localized
representation. The noncancellation/sign question is kept separate. -/
theorem thirdFullAxisRealThirdCommutator_exists_tube244
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ) ∧
      ∀ A B C : Freq244,
        fullSchwartzThirdCommutator244
            (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
          (thirdFullAxisRealFullCoefficientTube244 ρ hρ A B C δ).re := by
  let σ := lowNormalSixCenterSeparationRadius (1 : ℝ)
  have hσ : 0 < σ :=
    lowNormalSixCenterSeparationRadius_pos (1 : ℝ) (by norm_num)
  let ρ := min δ σ / 2
  have hρ : 0 < ρ := half_pos (lt_min hδ hσ)
  have hSmall : ρ ≤ σ := by
    dsimp [ρ]
    linarith [min_le_right δ σ]
  have hρδ : ρ ≤ δ := by
    dsimp [ρ]
    linarith [min_le_left δ σ]
  refine ⟨ρ, hρ, hSmall, ?_⟩
  intro A B C
  exact thirdFullAxisRealThirdCommutator_eq_tube244
    ρ hρ hSmall δ hρδ A B C

end
end PrimeTensor.FirstMonomialTriad
