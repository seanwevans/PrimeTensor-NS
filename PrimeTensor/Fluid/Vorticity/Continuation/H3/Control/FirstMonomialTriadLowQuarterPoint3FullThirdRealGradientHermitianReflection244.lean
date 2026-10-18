import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealFullCoefficientTube244
import Mathlib.Tactic

/-!
# Hermitian reflection parity of the actual full-third real gradient spectrum

The coherent-tube proof has already identified the complete physical third
commutator with a Fourier integral on twelve frequency-pair sectors. Here we
prove the *actual* constructed real velocity's Fourier spectrum has conjugate
reflection symmetry, and transport this symmetry through the literal seven-
derivative (3+3+1) gradient kernel. Seven odd frequency factors contribute
one minus sign, hence K(-p,-r) = -conj(K(p,r)). The seventh-power Fourier
phase is imaginary, so its REAL signed contribution is even under reflection.

This is an exact symmetry for arbitrary width and polarizations, not a sign
estimate for a coherent tube and not a claim of full noncancellation.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Topology

noncomputable section
set_option maxHeartbeats 1000000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev Pair244 := Freq244 × Freq244
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdReflect244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- EXACT Hermitian reflection of the *recovered physical real velocity's*
Fourier vector. No additional realness assumption is introduced. -/
theorem thirdFullAxisRealSpectrum_reflect244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : Freq244) :
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C (-ξ) =
      fun j => star (thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C ξ j) := by
  rw [thirdFullAxisRealSchwartzSpectrum_eq_packet244]
  rw [thirdFullAxisSixFourierPacket_reality244]
  funext j
  rw [thirdFullAxisRealSchwartzSpectrum_eq_packet244]

/-- Conservation q=-p-r is compatible with negating BOTH independent
frequencies; this is a genuine momentum-plane involution. -/
theorem thirdFullMiddleFrequency_pair_reflect244 (z : Pair244) :
    thirdFullMiddleFrequency244 (-z.1, -z.2) =
      -thirdFullMiddleFrequency244 z := by
  funext j
  simp only [thirdFullMiddleFrequency244, Pi.neg_apply]
  ring

/-- Every factor in the seven-derivative multiplier is a REAL frequency
contraction; conjugation leaves the complete polynomial unchanged. -/
theorem thirdFullGradientSevenWeight_star244
    (a b c d e k v : V3) (z : V3 × V3) :
    star (thirdFullGradientSevenWeight244 a b c d e k v z) =
      thirdFullGradientSevenWeight244 a b c d e k v z := by
  -- `star_mul'` is the multiplicative conjugation lemma available in
  -- this mathlib version. All seven factors are real-to-complex casts.
  simp [thirdFullGradientSevenWeight244, star_mul', Complex.conj_ofReal]

/-- Seven frequency derivatives give exactly ONE minus sign under simultaneous
frequency reflection. The q=-p-r dependency is respected. -/
theorem thirdFullGradientSevenWeight_reflect244
    (a b c d e k v : V3) (z : V3 × V3) :
    thirdFullGradientSevenWeight244 a b c d e k v (-z.1, -z.2) =
      -thirdFullGradientSevenWeight244 a b c d e k v z := by
  have hq : -((-z.1) + (-z.2)) = -(-(z.1 + z.2)) := by
    abel
  dsimp [thirdFullGradientSevenWeight244]
  rw [hq]
  simp only [inner_neg_left, Complex.ofReal_neg]
  ring

/-- The LITERAL Schwartz 3+3+1 kernel is odd-conjugate under simultaneous
reflection, not just its formal polynomial or sharp center value. -/
theorem thirdFullAxisRealGradientSlot_reflect244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j m n : A3) (a b c d e k v : V3) (z : V3 × V3) :
    thirdFullAxisRealGradientSlot244 ρ hρ A B C
        j m n a b c d e k v (-z.1, -z.2) =
      -star (thirdFullAxisRealGradientSlot244 ρ hρ A B C
        j m n a b c d e k v z) := by
  simp only [thirdFullAxisRealGradientSlot_factor244]
  rw [thirdFullGradientSevenWeight_reflect244]
  simp only [WithLp.ofLp_neg]
  -- The theorem quantifies a single pair. Instantiate it explicitly:
  -- `rw` cannot infer the shared pair metavariable from two projections.
  have hMiddle :
      thirdFullMiddleFrequency244
        (-(WithLp.ofLp z.1), -(WithLp.ofLp z.2)) =
      -(thirdFullMiddleFrequency244
        (WithLp.ofLp z.1, WithLp.ofLp z.2)) :=
    thirdFullMiddleFrequency_pair_reflect244
      (WithLp.ofLp z.1, WithLp.ofLp z.2)
  rw [hMiddle]
  simp only [thirdFullAxisRealSpectrum_reflect244, Pi.neg_apply,
    star_mul', thirdFullGradientSevenWeight_star244]
  ring

/-- For the real Fourier normalization, the seventh derivative phase is
purely imaginary. Odd-conjugate kernel reflection leaves its REAL part fixed. -/
theorem thirdFullSeventhPhase_oddConj_re244 (w : ℂ) :
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 * (-star w)).re =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 * w).re := by
  rw [h3FirstMonomial_fourier_phase]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, zero_sub, one_mul, neg_mul]
  ring

/-- The signed REAL seven-derivative Fourier density is EVEN under
reflection for every gradient component and every derivative direction. -/
theorem thirdFullAxisRealGradientSlot_signed_reflect244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j m n : A3) (a b c d e k v : V3) (z : V3 × V3) :
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      thirdFullAxisRealGradientSlot244 ρ hρ A B C
        j m n a b c d e k v (-z.1, -z.2)).re =
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      thirdFullAxisRealGradientSlot244 ρ hρ A B C
        j m n a b c d e k v z).re := by
  rw [thirdFullAxisRealGradientSlot_reflect244]
  exact thirdFullSeventhPhase_oddConj_re244 _

end
end PrimeTensor.FirstMonomialTriad
