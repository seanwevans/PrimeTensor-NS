import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdOrderedTriadSymbol244
import Mathlib.Tactic

/-!
# Six-permutation contraction of the COMPLETE third-order ordered symbol

The preceding ordered calculation yields 14 at one solenoidal momentum triad.
A nonzero ordered coefficient alone says nothing about the *six* momentum
permutations entering the Fourier trilinear integral.

We now simultaneously permute the three frequencies and their polarization
vectors in the EXACT real seven-derivative polynomial of that module. The
explicit solenoidal triad has the six coefficients

  14, -2, -57, 9, -294, 234,

so the total is -96, not zero. This is algebraic noncancellation of the fully
six-permuted ordered REAL polynomial, not an assertion about the complex,
Hermitian Schwartz Fourier integral. The seven Fourier derivatives produce
an odd power of i, and real-valued Schwartz fields impose conjugate-reflected
frequency contributions. Their phases and localization are separate tasks.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 400000

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeThirdSixSymbol244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- All six simultaneous permutations of three frequency/polarization
pairs. The order is pqr, prq, qpr, qrp, rpq, rqp. We do not average them. -/
noncomputable def thirdFullSixPermutationSymbol244
    (p q r A B C : A3 → ℝ) : ℝ :=
  thirdFullOrderedTriadRealSymbol244 p q r A B C +
  thirdFullOrderedTriadRealSymbol244 p r q A C B +
  thirdFullOrderedTriadRealSymbol244 q p r B A C +
  thirdFullOrderedTriadRealSymbol244 q r p B C A +
  thirdFullOrderedTriadRealSymbol244 r p q C A B +
  thirdFullOrderedTriadRealSymbol244 r q p C B A

/-- Swapping the first two frequency/polarization pairs simply permutes
the six summands. No momentum or solenoidality hypotheses are needed. -/
theorem thirdFullSixPermutationSymbol_swap_first244
    (p q r A B C : A3 → ℝ) :
    thirdFullSixPermutationSymbol244 q p r B A C =
      thirdFullSixPermutationSymbol244 p q r A B C := by
  unfold thirdFullSixPermutationSymbol244
  ring

/-- The same six-term coefficient is invariant under swapping the final
two paired frequencies and polarizations. -/
theorem thirdFullSixPermutationSymbol_swap_last244
    (p q r A B C : A3 → ℝ) :
    thirdFullSixPermutationSymbol244 p r q A C B =
      thirdFullSixPermutationSymbol244 p q r A B C := by
  unfold thirdFullSixPermutationSymbol244
  ring

/-- The ordered derivative polynomial has total ODD frequency degree seven.
Its signed coordinate contraction reverses sign when p,q,r are reflected,
provided polarizations are held fixed. -/
theorem thirdFullOrderedTriadRealSymbol_reflect_frequencies244
    (p q r A B C : A3 → ℝ) :
    thirdFullOrderedTriadRealSymbol244
      (fun i => -p i) (fun i => -q i) (fun i => -r i) A B C =
        -thirdFullOrderedTriadRealSymbol244 p q r A B C := by
  have hpq : thirdTriadAxisDot244 (fun i => -p i) (fun i => -q i) =
      thirdTriadAxisDot244 p q := by
    unfold thirdTriadAxisDot244
    simp only [neg_mul_neg]
  have hpr : thirdTriadAxisDot244 (fun i => -p i) (fun i => -r i) =
      thirdTriadAxisDot244 p r := by
    unfold thirdTriadAxisDot244
    simp only [neg_mul_neg]
  have hBr : thirdTriadAxisDot244 B (fun i => -r i) =
      -thirdTriadAxisDot244 B r := by
    unfold thirdTriadAxisDot244
    simp only [mul_neg, Finset.sum_neg_distrib]
  rw [thirdFullOrderedTriadRealSymbol_eq244,
      thirdFullOrderedTriadRealSymbol_eq244, hpq, hpr, hBr]
  ring

/-- Reflecting all frequencies flips the entire six-permutation symbol,
not just its original ordered summand. -/
theorem thirdFullSixPermutationSymbol_reflect_frequencies244
    (p q r A B C : A3 → ℝ) :
    thirdFullSixPermutationSymbol244
      (fun i => -p i) (fun i => -q i) (fun i => -r i) A B C =
        -thirdFullSixPermutationSymbol244 p q r A B C := by
  unfold thirdFullSixPermutationSymbol244
  rw [thirdFullOrderedTriadRealSymbol_reflect_frequencies244,
    thirdFullOrderedTriadRealSymbol_reflect_frequencies244,
    thirdFullOrderedTriadRealSymbol_reflect_frequencies244,
    thirdFullOrderedTriadRealSymbol_reflect_frequencies244,
    thirdFullOrderedTriadRealSymbol_reflect_frequencies244,
    thirdFullOrderedTriadRealSymbol_reflect_frequencies244]
  ring

/-- The actual recursive positive-depth axis coordinates used in the
committed single-order witness, reconstructed here because its identifiers
are private to the preceding module. -/
private def sixCoord244 (x y z : ℝ) (i : A3) : ℝ :=
  if axisRank i = 0 then x else if axisRank i = 1 then y else z

private def p6 : A3 → ℝ := sixCoord244 1 0 0
private def q6 : A3 → ℝ := sixCoord244 1 1 0
private def r6 : A3 → ℝ := sixCoord244 (-2) (-1) 0
private def A6 : A3 → ℝ := sixCoord244 0 1 0
private def B6 : A3 → ℝ := sixCoord244 1 (-1) 0
private def C6 : A3 → ℝ := sixCoord244 1 (-2) 0

/-- Dot products of actual positive-axis coordinate functions are ordinary
three-dimensional Euclidean dot products, with no `Fin 3` substitution. -/
private theorem sixCoord_dot244
    (ax ay az bx byCoord bz : ℝ) :
    thirdTriadAxisDot244 (sixCoord244 ax ay az)
      (sixCoord244 bx byCoord bz) =
        ax * bx + ay * byCoord + az * bz := by
  classical
  unfold thirdTriadAxisDot244
  rw [axis_sum_three]
  norm_num [sixCoord244, axisRank, xAxis, yAxis, zAxis] <;> ring

/-- The same genuine momentum-conserving and solenoidal polarizations as
the single-order theorem. All three dot-product constraints are exact. -/
theorem thirdFullSixSymbol_solenoidal_triads244 :
    (∀ i : A3, p6 i + q6 i + r6 i = 0) ∧
    thirdTriadAxisDot244 A6 p6 = 0 ∧
    thirdTriadAxisDot244 B6 q6 = 0 ∧
    thirdTriadAxisDot244 C6 r6 = 0 := by
  constructor
  · intro i
    cases i with
    | first =>
        norm_num [p6, q6, r6, sixCoord244, axisRank]
    | next i =>
        cases i with
        | first =>
            norm_num [p6, q6, r6, sixCoord244, axisRank]
        | next i =>
            cases i with
            | first =>
                norm_num [p6, q6, r6, sixCoord244, axisRank]
  · constructor
    · norm_num [A6, p6, sixCoord_dot244]
    · constructor
      · norm_num [B6, q6, sixCoord_dot244]
      · norm_num [C6, r6, sixCoord_dot244]

/-- Every permutation is computed separately, not inferred by multiplying
the original ordered coefficient by six. These values have substantial
signed cancellation but their sum does not vanish. -/
theorem thirdFullSixSymbol_each_permutation244 :
    thirdFullOrderedTriadRealSymbol244 p6 q6 r6 A6 B6 C6 = 14 ∧
    thirdFullOrderedTriadRealSymbol244 p6 r6 q6 A6 C6 B6 = -2 ∧
    thirdFullOrderedTriadRealSymbol244 q6 p6 r6 B6 A6 C6 = -57 ∧
    thirdFullOrderedTriadRealSymbol244 q6 r6 p6 B6 C6 A6 = 9 ∧
    thirdFullOrderedTriadRealSymbol244 r6 p6 q6 C6 A6 B6 = -294 ∧
    thirdFullOrderedTriadRealSymbol244 r6 q6 p6 C6 B6 A6 = 234 := by
  simp only [thirdFullOrderedTriadRealSymbol_eq244]
  simp only [p6, q6, r6, A6, B6, C6, sixCoord_dot244]
  norm_num

/-- The fully six-permuted REAL third-order derivative symbol of this
solenoidal triad equals -96: it is NOT killed by algebraic symmetrization. -/
theorem thirdFullSixSymbol_nonzero_solenoidal244 :
    thirdFullSixPermutationSymbol244 p6 q6 r6 A6 B6 C6 = -96 := by
  rcases thirdFullSixSymbol_each_permutation244 with
    ⟨h1, h2, h3, h4, h5, h6⟩
  unfold thirdFullSixPermutationSymbol244
  rw [h1, h2, h3, h4, h5, h6]
  norm_num

/-- An explicitly nonzero six-permutation derivative symbol is a necessary
finite-dimensional input for a full Fourier-packet noncancellation argument.
No physical integral equality or Hermitian localization is claimed here. -/
theorem thirdFullSixSymbol_nonzero244 :
    thirdFullSixPermutationSymbol244 p6 q6 r6 A6 B6 C6 ≠ 0 := by
  rw [thirdFullSixSymbol_nonzero_solenoidal244]
  norm_num

end
end PrimeTensor.FirstMonomialTriad
