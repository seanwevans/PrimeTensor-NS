import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSectorInterpolationPhase244
import Mathlib.Tactic

/-!
# Full third physical H3 gradient polynomial on six positive sectors

The genuine seven-derivative 3+3+1 channel is a five-index sum of FOUR
physical derivative slots, with its energy coefficient two. Each Fourier
triple has already been proved to have imaginary phase I on a positive
coherent sector when the actual triple mass is nonzero. We now retain the
four original index patterns and explicitly assemble ALL five finite sums
into an exact real variable-frequency polynomial. Then the true 3+2+2
interpolation polynomial is added with its physical factor six.

This is an identity for the actual real divergence-free Schwartz velocity.
It is not a sign or noncancellation theorem. In particular the center
value -192 does not control these integrals without further estimates.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairV244 := H3FourierPoint3 × H3FourierPoint3

noncomputable local instance axisFintypeSectorGradientPolynomial244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Imaginary part of a literal four-term complex sum multiplied by the
physical REAL energy coefficient two. The nesting exactly matches the
original gradient-axis unphased definition. -/
private theorem thirdFullImag_two_four244 (u v w x : ℂ) :
    ((2 : ℂ) * (((u + v) + w) + x)).im =
      2 * (((u.im + v.im) + w.im) + x.im) := by
  simp only [Complex.mul_im, Complex.add_im]
  norm_num

/-- The COMPLETE four-pattern physical gradient block at one ordered
five-index axis label, written as a real polynomial in the original
seven-derivative weights and the actual windowed transverse-germ triple.
No terms are dropped and none are symmetrized. -/
noncomputable def thirdFullPositiveSectorGradientAxisReal244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) (j i k l r : A3) : ℝ :=
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  2 * (((
    (thirdFullGradientSevenWeight244 a b c a b c d z).re *
      thirdFullPositiveSectorRealTripleFactor244 ρ hρ A B C n z j r j +
    (thirdFullGradientSevenWeight244 a b c a b d c z).re *
      thirdFullPositiveSectorRealTripleFactor244 ρ hρ A B C n z j j r) +
    (thirdFullGradientSevenWeight244 a b c a d c b z).re *
      thirdFullPositiveSectorRealTripleFactor244 ρ hρ A B C n z j j r) +
    (thirdFullGradientSevenWeight244 a b c d b c a z).re *
      thirdFullPositiveSectorRealTripleFactor244 ρ hρ A B C n z j j r)

/-- Exact REAL formula for the imaginary part of one COMPLETE physical
gradient-axis block. It uses four previously proved literal seven-derivative
Fourier-slot identities, rather than an independent sharp symbol. -/
theorem thirdFullPositiveSector_gradient_axis_imag244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0)
    (j i k l r : A3) :
    (thirdFullAxisRealGradientAxisUnphased244 ρ hρ A B C j i k l r z).im =
      thirdFullPositiveSectorGradientAxisReal244 ρ hρ A B C n z j i k l r := by
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  have h1 := thirdFullPositiveSector_gradient_slot_imag244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass
    j r j a b c a b c d
  have h2 := thirdFullPositiveSector_gradient_slot_imag244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass
    j j r a b c a b d c
  have h3 := thirdFullPositiveSector_gradient_slot_imag244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass
    j j r a b c a d c b
  have h4 := thirdFullPositiveSector_gradient_slot_imag244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass
    j j r a b c d b c a
  change ((2 : ℂ) * (((
    thirdFullAxisRealGradientSlot244 ρ hρ A B C j r j
      a b c a b c d z +
    thirdFullAxisRealGradientSlot244 ρ hρ A B C j j r
      a b c a b d c z) +
    thirdFullAxisRealGradientSlot244 ρ hρ A B C j j r
      a b c a d c b z) +
    thirdFullAxisRealGradientSlot244 ρ hρ A B C j j r
      a b c d b c a z)).im = _
  rw [thirdFullImag_two_four244, h1, h2, h3, h4]
  -- Only unfold the right-hand four-pattern real polynomial.
  rfl

/-- Five-index sum over all three physical axes in each index position.
This is the complete 3+3+1 gradient polynomial, including its energy
coefficient two, not a selected component or a six-order surrogate. -/
noncomputable def thirdFullPositiveSectorGradientTotalReal244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
    thirdFullPositiveSectorGradientAxisReal244 ρ hρ A B C n z j i k l r

/-- The imaginary part of a finite complex sum equals the sum of the
imaginary parts. Use an elementary induction rather than relying on a
library lemma name that differs across mathlib versions. -/
private theorem thirdFullFinsetSumImag244 {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) :
    (s.sum f).im = s.sum (fun x => (f x).im) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    simp [Finset.sum_insert, hx, ih, Complex.add_im]

/-- The original full physical 3+3+1 Fourier gradient total is EXACTLY
this five-index real polynomial at each nonzero coherent sector point. -/
theorem thirdFullPositiveSector_gradient_total_imag244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0) :
    (thirdFullAxisRealGradientTotalUnphased244 ρ hρ A B C z).im =
      thirdFullPositiveSectorGradientTotalReal244 ρ hρ A B C n z := by
  unfold thirdFullAxisRealGradientTotalUnphased244
    thirdFullPositiveSectorGradientTotalReal244
  simp only [thirdFullFinsetSumImag244]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  exact thirdFullPositiveSector_gradient_axis_imag244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass j i k l r

/-- The entire seven-derivative physical real polynomial, now combining
all five-index 3+3+1 gradient terms with the TRUE 3+2+2 interpolation
coefficient and its literal multiplier SIX. This retains the three moving
solenoidal polarizations and the full Schwartz frequency-window product. -/
noncomputable def thirdFullPositiveSectorPhysicalPolynomial244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) : ℝ :=
  thirdFullPositiveSectorGradientTotalReal244 ρ hρ A B C n z +
    6 * thirdFullPositiveSectorInterpolationReal244 ρ hρ A B C n z

/-- The actual full third H3 physical Fourier commutator integrand equals
one explicit REAL variable-frequency polynomial at each nonzero point of
any of the SIX positive coherent sectors. This is a sign-neutral identity,
not an assumption that the six integrals are negative. -/
theorem thirdFullPositiveSector_full_imag_eq_physical_polynomial244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0) :
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im =
      thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z := by
  rw [thirdFullPositiveSector_full_imag_eq_gradient_plus_interpolation244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass]
  rw [thirdFullPositiveSector_gradient_total_imag244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass]
  rfl

end
end PrimeTensor.FirstMonomialTriad
