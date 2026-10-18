import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdAxisWindowSupport244
import Mathlib.Tactic

/-!
# Coherent-sector permutation and reflected-phase identities

The axis-window support theorem rules out every noncoherent labeled triad.
For coherent triads the corrected six-order polynomial must be invariant
under simultaneously relabeling the momenta and their moving solenoidal
polarizations. It must also be paired with its reflected sector using the
CONJUGATED complex phase, not by treating the odd-frequency symbol as even.

This file establishes these exact pointwise identities on the genuine
`Axis Depth.three` Fourier carrier. It does NOT identify the complete
Schwartz Fourier integral with a sum of these orbit values and does NOT
claim global noncancellation or Navier--Stokes continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Pair244 := (A3 → ℝ) × (A3 → ℝ)

noncomputable local instance axisFintypeCoherentPhase244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The CORRECTED full physical six-order symbol is unchanged by swapping
its first two frequency/polarization pairs. -/
theorem thirdFullPhysicalSix_swap_first_coherent244
    (p q r A B C : A3 → ℝ) :
    thirdFullPhysicalSixSymbol244 q p r B A C =
      thirdFullPhysicalSixSymbol244 p q r A B C := by
  rw [thirdFullPhysicalSix_eq_prior_six244,
    thirdFullPhysicalSix_eq_prior_six244]
  exact thirdFullSixPermutationSymbol_swap_first244 p q r A B C

/-- The same symmetry for the last two paired momentum modes. -/
theorem thirdFullPhysicalSix_swap_last_coherent244
    (p q r A B C : A3 → ℝ) :
    thirdFullPhysicalSixSymbol244 p r q A C B =
      thirdFullPhysicalSixSymbol244 p q r A B C := by
  rw [thirdFullPhysicalSix_eq_prior_six244,
    thirdFullPhysicalSix_eq_prior_six244]
  exact thirdFullSixPermutationSymbol_swap_last244 p q r A B C

/-- Conservation is preserved when the dependent middle momentum and the
first momentum exchange roles. -/
theorem thirdFullMiddleFrequency_swap_first_coherent244 (z : Pair244) :
    thirdFullMiddleFrequency244 (thirdFullMiddleFrequency244 z, z.2) = z.1 := by
  funext i
  dsimp [thirdFullMiddleFrequency244]
  ring

/-- Conservation also survives swapping the second and third momenta. -/
theorem thirdFullMiddleFrequency_swap_last_coherent244 (z : Pair244) :
    thirdFullMiddleFrequency244 (z.1, thirdFullMiddleFrequency244 z) = z.2 := by
  funext i
  dsimp [thirdFullMiddleFrequency244]
  ring

/-- The moving-polarization six-order Hermitian coefficient is invariant
under swapping the first two modes AND their separate projection centers.
No frozen-center divergence-free approximation is used. -/
theorem thirdFullProjectedHermitianKernel_swap_first_coherent244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) :
    thirdFullProjectedHermitianKernel244 q₀ p₀ r₀ B A C
      (thirdFullMiddleFrequency244 z, z.2) =
    thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z := by
  have hm := thirdFullMiddleFrequency_swap_first_coherent244 z
  unfold thirdFullProjectedHermitianKernel244
  simp only [hm, thirdFullHermitianMomentumKernel_eq244]
  rw [thirdFullPhysicalSix_swap_first_coherent244]

/-- The same invariance under exchange of the last two modes, including
frequency-by-frequency projected polarizations. -/
theorem thirdFullProjectedHermitianKernel_swap_last_coherent244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) :
    thirdFullProjectedHermitianKernel244 p₀ r₀ q₀ A C B
      (z.1, thirdFullMiddleFrequency244 z) =
    thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z := by
  have hm := thirdFullMiddleFrequency_swap_last_coherent244 z
  unfold thirdFullProjectedHermitianKernel244
  simp only [hm, thirdFullHermitianMomentumKernel_eq244]
  rw [thirdFullPhysicalSix_swap_last_coherent244]

/-- The actual three indexed smooth windows multiply the fully projected,
corrected seven-derivative Hermitian kernel. Distinct labels retain distinct
scalar cutoffs, unlike a single shared weight used at every frequency. -/
noncomputable def thirdFullLabelledWindowedProjectedKernel_coherent244
    (ρ : ℝ) (hρ : 0 < ρ) (i j k : Fin 6)
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) : ℝ :=
  ((thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) z.1 *
    (thirdFullAxisWindowBump244 ρ hρ j : (A3 → ℝ) → ℝ)
      (thirdFullMiddleFrequency244 z) *
    (thirdFullAxisWindowBump244 ρ hρ k : (A3 → ℝ) → ℝ) z.2) *
    thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z

/-- Support exclusion now annihilates the WHOLE labelled corrected
Hermitian coefficient, not merely its three scalar window factors. -/
theorem thirdFullLabelledWindowedProjectedKernel_noncoherent_zero244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (i j k : Fin 6) (hNon : ¬ lowNormalCoherentCenters i j k)
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) :
    thirdFullLabelledWindowedProjectedKernel_coherent244
      ρ hρ i j k p₀ q₀ r₀ A B C z = 0 := by
  unfold thirdFullLabelledWindowedProjectedKernel_coherent244
  rw [thirdFullAxisWindowBump_noncoherent_product_zero244
    ρ hρ hSmall i j k hNon z]
  ring

/-- Relabel the first two windows AND their moving polarization germs.
The complete windowed signed coefficient is unchanged, pointwise. -/
theorem thirdFullLabelledWindowedProjectedKernel_swap_first244
    (ρ : ℝ) (hρ : 0 < ρ) (i j k : Fin 6)
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) :
    thirdFullLabelledWindowedProjectedKernel_coherent244
      ρ hρ j i k q₀ p₀ r₀ B A C
      (thirdFullMiddleFrequency244 z, z.2) =
    thirdFullLabelledWindowedProjectedKernel_coherent244
      ρ hρ i j k p₀ q₀ r₀ A B C z := by
  unfold thirdFullLabelledWindowedProjectedKernel_coherent244
  rw [thirdFullMiddleFrequency_swap_first_coherent244,
    thirdFullProjectedHermitianKernel_swap_first_coherent244]
  ring

/-- The same complete labelled coefficient is unchanged under swapping
the last two windowed momentum-polarization pairs. -/
theorem thirdFullLabelledWindowedProjectedKernel_swap_last244
    (ρ : ℝ) (hρ : 0 < ρ) (i j k : Fin 6)
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) :
    thirdFullLabelledWindowedProjectedKernel_coherent244
      ρ hρ i k j p₀ r₀ q₀ A C B
      (z.1, thirdFullMiddleFrequency244 z) =
    thirdFullLabelledWindowedProjectedKernel_coherent244
      ρ hρ i j k p₀ q₀ r₀ A B C z := by
  unfold thirdFullLabelledWindowedProjectedKernel_coherent244
  rw [thirdFullMiddleFrequency_swap_last_coherent244,
    thirdFullProjectedHermitianKernel_swap_last_coherent244]
  ring

/-- Negating both arguments of the Euclidean dot preserves its value. -/
theorem thirdFullAxisDot_neg_neg_coherent244 (u v : A3 → ℝ) :
    thirdTriadAxisDot244 (fun i => -u i) (fun i => -v i) =
      thirdTriadAxisDot244 u v := by
  unfold thirdTriadAxisDot244
  simp only [neg_mul_neg]

/-- Negating only the first dot argument reverses its sign. -/
theorem thirdFullAxisDot_neg_left_coherent244 (u v : A3 → ℝ) :
    thirdTriadAxisDot244 (fun i => -u i) v =
      -thirdTriadAxisDot244 u v := by
  unfold thirdTriadAxisDot244
  simp only [neg_mul, Finset.sum_neg_distrib]

/-- The polynomial Leray numerator has even frequency parity when its
physical polarization remains fixed. This holds even at zero frequency. -/
theorem thirdFullTransversePolynomial_reflect_coherent244 (ξ a : A3 → ℝ) :
    thirdFullTransversePolynomial244 (fun i => -ξ i) a =
      thirdFullTransversePolynomial244 ξ a := by
  have hSq := thirdFullAxisDot_neg_neg_coherent244 ξ ξ
  have hMix := thirdFullAxisDot_neg_left_coherent244 ξ a
  funext i
  change thirdTriadAxisDot244 (fun j => -ξ j) (fun j => -ξ j) * a i -
      thirdTriadAxisDot244 (fun j => -ξ j) a * (-ξ i) =
    thirdTriadAxisDot244 ξ ξ * a i - thirdTriadAxisDot244 ξ a * ξ i
  rw [hSq, hMix]
  ring

/-- The normalizing denominator is evaluated at a FIXED center, so
reflecting both the center and current frequency preserves the exact
transverse germ. In particular no reciprocal-frequency singularity appears. -/
theorem thirdFullFixedCenterTransverseGerm_reflect_coherent244
    (η ξ a : A3 → ℝ) :
    thirdFullFixedCenterTransverseGerm244
      (fun i => -η i) (fun i => -ξ i) a =
    thirdFullFixedCenterTransverseGerm244 η ξ a := by
  have hSq := thirdFullAxisDot_neg_neg_coherent244 η η
  have hP := thirdFullTransversePolynomial_reflect_coherent244 ξ a
  funext i
  change (thirdTriadAxisDot244 (fun j => -η j) (fun j => -η j))⁻¹ *
      thirdFullTransversePolynomial244 (fun j => -ξ j) a i =
    (thirdTriadAxisDot244 η η)⁻¹ *
      thirdFullTransversePolynomial244 ξ a i
  rw [hSq, hP]

/-- The momentum-dependent middle frequency reverses under simultaneous
reflection of the two independent Fourier variables. -/
theorem thirdFullMiddleFrequency_reflect_coherent244 (z : Pair244) :
    thirdFullMiddleFrequency244
      ((fun i => -z.1 i), (fun i => -z.2 i)) =
    (fun i => -(thirdFullMiddleFrequency244 z i)) := by
  funext i
  dsimp [thirdFullMiddleFrequency244]
  ring

/-- Full seventh-derivative Hermitian phase bookkeeping: an odd real
frequency polynomial and the imaginary part of the conjugated phase each
change sign, leaving their PRODUCT invariant. This is an algebraic
reflected-sector identity, not an integral equality. -/
theorem thirdFullPhysicalHermitianOrbit_reflect_conj_coherent244
    (p q r A B C : A3 → ℝ) (phase : ℂ) :
    thirdFullPhysicalHermitianOrbit244
      (fun i => -p i) (fun i => -q i) (fun i => -r i)
      A B C (star phase) =
    thirdFullPhysicalHermitianOrbit244 p q r A B C phase := by
  simp only [thirdFullPhysicalHermitianOrbit_eq244,
    thirdFullPhysicalSix_reflection244, Complex.star_def, Complex.conj_im]
  ring

/-- The full moving-polarization Hermitian coefficient with an ARBITRARY
complex scalar product phase, rather than only the sharp phase `I`. -/
noncomputable def thirdFullMovingHermitianOrbit_coherent244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) (phase : ℂ) : ℝ :=
  thirdFullPhysicalHermitianOrbit244
    z.1 (thirdFullMiddleFrequency244 z) z.2
    (thirdFullFixedCenterTransverseGerm244 p₀ z.1 A)
    (thirdFullFixedCenterTransverseGerm244 q₀
      (thirdFullMiddleFrequency244 z) B)
    (thirdFullFixedCenterTransverseGerm244 r₀ z.2 C)
    phase

/-- The existing projected Hermitian kernel is EXACTLY the moving orbit
at the imaginary scalar phase I, without an extra factor of two. -/
theorem thirdFullMovingHermitianOrbit_I_coherent244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) :
    thirdFullMovingHermitianOrbit_coherent244 p₀ q₀ r₀ A B C z Complex.I =
      thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z := by
  rfl

/-- A phase-free formula shows explicitly why setting all Fourier amplitudes
real (Im phase = 0) would kill this odd-frequency Hermitian orbit. -/
theorem thirdFullMovingHermitianOrbit_phase_coherent244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) (phase : ℂ) :
    thirdFullMovingHermitianOrbit_coherent244 p₀ q₀ r₀ A B C z phase =
      phase.im * thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z := by
  rw [thirdFullMovingHermitianOrbit_coherent244,
    thirdFullPhysicalHermitianOrbit_eq244,
    ← thirdFullMovingHermitianOrbit_I_coherent244]
  rw [thirdFullMovingHermitianOrbit_coherent244,
    thirdFullPhysicalHermitianOrbit_eq244]
  simp only [Complex.I_im]
  ring

/-- EXACT reflected-sector pairing for three independently moving
solenoidal polarizations. A reflected triple must carry conjugate phase;
its Hermitian physical contribution then agrees with the original. -/
theorem thirdFullMovingHermitianOrbit_reflect_conj_coherent244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) (phase : ℂ) :
    thirdFullMovingHermitianOrbit_coherent244
      (fun i => -p₀ i) (fun i => -q₀ i) (fun i => -r₀ i)
      A B C ((fun i => -z.1 i), (fun i => -z.2 i)) (star phase) =
    thirdFullMovingHermitianOrbit_coherent244 p₀ q₀ r₀ A B C z phase := by
  have hm := thirdFullMiddleFrequency_reflect_coherent244 z
  unfold thirdFullMovingHermitianOrbit_coherent244
  rw [hm,
    thirdFullFixedCenterTransverseGerm_reflect_coherent244,
    thirdFullFixedCenterTransverseGerm_reflect_coherent244,
    thirdFullFixedCenterTransverseGerm_reflect_coherent244]
  exact thirdFullPhysicalHermitianOrbit_reflect_conj_coherent244
    z.1 (thirdFullMiddleFrequency244 z) z.2
    (thirdFullFixedCenterTransverseGerm244 p₀ z.1 A)
    (thirdFullFixedCenterTransverseGerm244 q₀
      (thirdFullMiddleFrequency244 z) B)
    (thirdFullFixedCenterTransverseGerm244 r₀ z.2 C) phase

end
end PrimeTensor.FirstMonomialTriad
