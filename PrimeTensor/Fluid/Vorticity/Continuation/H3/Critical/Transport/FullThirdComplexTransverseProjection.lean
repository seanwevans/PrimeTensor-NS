import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSchwartzLongitudinalFluxControl
import Mathlib.Tactic

/-!
# Complex Fourier transverse numerator and the high-high-low resonance

The full H³ flux is genuinely COMPLEX trilinear.  A real-only Leray-numerator
lemma cannot be silently applied to its Fourier polarizations.  We therefore
construct the complex-bilinear, denominator-free transverse numerator

    N_ξ(A) = (ξ·ξ) A - (ξ·A) ξ,

show its exact frequencywise divergence cancellation, and use it in the
actual unrestricted six-symbol.  A fixed-center inverse radius (never a
varying-frequency inverse) recovers transverse data at a nonzero anchor.

The final algebraic resonance theorem records why longitudinal and radial
fluxes cannot be separated without an additional analytic estimate: at
(p,0,-p) they cancel exactly, although each piece can be nonzero.

These are algebraic results; the density of *physical real Schwartz* fields
with the necessary exact matched derivative jets remains a distinct task.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeComplexTransverseProjection244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Complex-bilinear polarization dot against the real frequency is linear
in the polarization.  No conjugation is introduced. -/
private theorem thirdFullComplexMixedDot_const_mul244
    (ξ : A3 → ℝ) (A : A3 → ℂ) (c : ℂ) :
    mixedDot ξ (fun i => c * A i) = c * mixedDot ξ A := by
  unfold mixedDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem thirdFullComplexMixedDot_sub244
    (ξ : A3 → ℝ) (A B : A3 → ℂ) :
    mixedDot ξ (fun i => A i - B i) =
      mixedDot ξ A - mixedDot ξ B := by
  unfold mixedDot
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- The complex frequency-square is exactly the *real* axis dot cast into ℂ.
This is the bridge between the genuine complex Fourier polarization and the
existing real-frequency radial multiplier. -/
private theorem thirdFullComplexMixedDot_frequency244
    (ξ : A3 → ℝ) :
    mixedDot ξ (fun i => (ξ i : ℂ)) =
      (thirdTriadAxisDot244 ξ ξ : ℂ) := by
  change (∑ i : A3, (ξ i : ℂ) * (ξ i : ℂ)) =
    ((∑ i : A3, ξ i * ξ i : ℝ) : ℂ)
  push_cast
  rfl

/-- The polynomial transverse projection numerator on the ACTUAL complex
Fourier polarizations, globally defined even at zero frequency. -/
noncomputable def thirdFullComplexTransverseNumerator244
    (ξ : A3 → ℝ) (A : A3 → ℂ) (i : A3) : ℂ :=
  (thirdTriadAxisDot244 ξ ξ : ℂ) * A i -
    mixedDot ξ A * (ξ i : ℂ)

/-- Exact Fourier incompressibility with no division by frequency. -/
theorem thirdFullComplexTransverseNumerator_divergence244
    (ξ : A3 → ℝ) (A : A3 → ℂ) :
    mixedDot ξ (thirdFullComplexTransverseNumerator244 ξ A) = 0 := by
  change mixedDot ξ (fun i =>
    (thirdTriadAxisDot244 ξ ξ : ℂ) * A i -
      mixedDot ξ A * (ξ i : ℂ)) = 0
  rw [thirdFullComplexMixedDot_sub244,
    thirdFullComplexMixedDot_const_mul244,
    thirdFullComplexMixedDot_const_mul244,
    thirdFullComplexMixedDot_frequency244]
  ring

/-- A transverse complex polarization is reproduced up to the squared
frequency factor, just as in the real polynomial lift. -/
theorem thirdFullComplexTransverseNumerator_at_transverse244
    (ξ : A3 → ℝ) (A : A3 → ℂ)
    (hA : mixedDot ξ A = 0) :
    thirdFullComplexTransverseNumerator244 ξ A =
      fun i => (thirdTriadAxisDot244 ξ ξ : ℂ) * A i := by
  funext i
  simp only [thirdFullComplexTransverseNumerator244, hA, zero_mul, sub_zero]

/-- The numerator vanishes at zero frequency rather than introducing a
singular Leray denominator there. -/
theorem thirdFullComplexTransverseNumerator_at_zero244
    (A : A3 → ℂ) :
    thirdFullComplexTransverseNumerator244 (fun _ => 0) A =
      fun _ => 0 := by
  funext i
  simp [thirdFullComplexTransverseNumerator244,
    thirdTriadAxisDot244, mixedDot]

/-- The polynomial numerator is a scaled projection: Nξ² = |ξ|² Nξ.
This identity is exact also for ξ = 0. -/
theorem thirdFullComplexTransverseNumerator_square244
    (ξ : A3 → ℝ) (A : A3 → ℂ) :
    thirdFullComplexTransverseNumerator244 ξ
        (thirdFullComplexTransverseNumerator244 ξ A) =
      fun i => (thirdTriadAxisDot244 ξ ξ : ℂ) *
        thirdFullComplexTransverseNumerator244 ξ A i :=
  thirdFullComplexTransverseNumerator_at_transverse244 ξ
    (thirdFullComplexTransverseNumerator244 ξ A)
    (thirdFullComplexTransverseNumerator_divergence244 ξ A)

/-- Normalization at a fixed (nonzero) center, avoiding the variable
frequency denominator found in the usual Leray symbol. -/
noncomputable def thirdFullComplexFixedCenterTransverseGerm244
    (η ξ : A3 → ℝ) (A : A3 → ℂ) (i : A3) : ℂ :=
  (thirdTriadAxisDot244 η η : ℂ)⁻¹ *
    thirdFullComplexTransverseNumerator244 ξ A i

/-- The normalized germ is still exactly transverse for every ξ. -/
theorem thirdFullComplexFixedCenterTransverseGerm_divergence244
    (η ξ : A3 → ℝ) (A : A3 → ℂ) :
    mixedDot ξ (thirdFullComplexFixedCenterTransverseGerm244 η ξ A) = 0 := by
  change mixedDot ξ (fun i =>
    (thirdTriadAxisDot244 η η : ℂ)⁻¹ *
      thirdFullComplexTransverseNumerator244 ξ A i) = 0
  rw [thirdFullComplexMixedDot_const_mul244,
    thirdFullComplexTransverseNumerator_divergence244]
  ring

/-- At a transverse, nonzero anchor the fixed-center germ reproduces the
COMPLEX polarization exactly. -/
theorem thirdFullComplexFixedCenterTransverseGerm_at_anchor244
    (η : A3 → ℝ) (A : A3 → ℂ)
    (hA : mixedDot η A = 0)
    (hη : (thirdTriadAxisDot244 η η : ℂ) ≠ 0) :
    thirdFullComplexFixedCenterTransverseGerm244 η η A = A := by
  funext i
  change (thirdTriadAxisDot244 η η : ℂ)⁻¹ *
    thirdFullComplexTransverseNumerator244 η A i = A i
  rw [thirdFullComplexTransverseNumerator_at_transverse244 η A hA]
  field_simp [hη]

/-- A full actual complex triad whose three amplitudes have been
polynomially transverse-projected has ZERO longitudinal correction.
This requires no solenoidality premise on A, B, or C beforehand. -/
theorem thirdFullComplexLongitudinalDefect_projected_zero244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) :
    thirdFullComplexLongitudinalFluxDefect244 p q r
      (thirdFullComplexTransverseNumerator244 p A)
      (thirdFullComplexTransverseNumerator244 q B)
      (thirdFullComplexTransverseNumerator244 r C) = 0 := by
  exact thirdFullComplexLongitudinalFluxDefect_zero_of_solenoidal244
    p q r _ _ _
    (thirdFullComplexTransverseNumerator_divergence244 p A)
    (thirdFullComplexTransverseNumerator_divergence244 q B)
    (thirdFullComplexTransverseNumerator_divergence244 r C)

/-- Consequently the actual SIX-PERMUTATION H³ complex symbol reduces to
its three-term sixth-power flux on the polynomially projected amplitudes. -/
theorem thirdFullComplexSix_projected_eq_flux244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0) :
    thirdFullComplexSixSymbol244 p q r
      (thirdFullComplexTransverseNumerator244 p A)
      (thirdFullComplexTransverseNumerator244 q B)
      (thirdFullComplexTransverseNumerator244 r C) =
    thirdFullComplexSixthPowerFlux244 p q r
      (thirdFullComplexTransverseNumerator244 p A)
      (thirdFullComplexTransverseNumerator244 q B)
      (thirdFullComplexTransverseNumerator244 r C) := by
  rw [thirdFullComplexSix_eq_flux_add_longitudinal244 p q r _ _ _ hm]
  rw [thirdFullComplexLongitudinalDefect_projected_zero244]
  ring

/-- An exact high-high-zero resonance: the 12 corrected complex orderings
vanish at momentum (p,0,-p), with NO divergence assumption on A,B,C. -/
theorem thirdFullComplexSix_zero_middle244
    (p : A3 → ℝ) (A B C : A3 → ℂ) :
    thirdFullComplexSixSymbol244 p (fun _ => 0)
      (fun i => -p i) A B C = 0 := by
  simp [thirdFullComplexSixSymbol244, thirdFullComplexOrderedSymbol244,
    thirdTriadAxisDot244, mixedDot]

/-- The radial flux itself does NOT generally vanish at the resonance:
its exact value is - (B·C)(p·A)|p|⁶. -/
theorem thirdFullComplexFlux_zero_middle244
    (p : A3 → ℝ) (A B C : A3 → ℂ) :
    thirdFullComplexSixthPowerFlux244 p (fun _ => 0)
      (fun i => -p i) A B C =
    -((thirdFullComplexPolarizationDot244 B C * mixedDot p A) *
      (thirdTriadAxisDot244 p p : ℂ) ^ 3) := by
  simp [thirdFullComplexSixthPowerFlux244, thirdTriadAxisDot244,
    mixedDot, Finset.sum_neg_distrib]

/-- The longitudinal correction is precisely the opposite of the radial
flux on the resonance, which is the analytic high-high-low warning. -/
theorem thirdFullComplexLongitudinalDefect_zero_middle244
    (p : A3 → ℝ) (A B C : A3 → ℂ) :
    thirdFullComplexLongitudinalFluxDefect244 p (fun _ => 0)
      (fun i => -p i) A B C =
    (thirdFullComplexPolarizationDot244 B C * mixedDot p A) *
      (thirdTriadAxisDot244 p p : ℂ) ^ 3 := by
  have hm : ∀ i, p i + (0 : ℝ) + -p i = 0 := by
    intro i
    ring
  have hSix := thirdFullComplexSix_eq_flux_add_longitudinal244
    p (fun _ => 0) (fun i => -p i) A B C hm
  rw [thirdFullComplexSix_zero_middle244,
    thirdFullComplexFlux_zero_middle244] at hSix
  calc
    thirdFullComplexLongitudinalFluxDefect244 p (fun _ => 0)
        (fun i => -p i) A B C =
      (-((thirdFullComplexPolarizationDot244 B C * mixedDot p A) *
          (thirdTriadAxisDot244 p p : ℂ) ^ 3) +
        thirdFullComplexLongitudinalFluxDefect244 p (fun _ => 0)
          (fun i => -p i) A B C) +
      (thirdFullComplexPolarizationDot244 B C * mixedDot p A) *
          (thirdTriadAxisDot244 p p : ℂ) ^ 3 := by ring
    _ = _ := by rw [← hSix]; ring

end
end PrimeTensor.FirstMonomialTriad
