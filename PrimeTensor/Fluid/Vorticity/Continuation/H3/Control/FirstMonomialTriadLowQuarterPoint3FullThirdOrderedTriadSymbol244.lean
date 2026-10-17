import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzFullGradientConcentration244
import Mathlib.Tactic

/-!
# The exact ordered Fourier triad derivative polynomial of G₃ + 3M

The previous theorem constructs the *physical Schwartz integral* G₃ + 3M,
but leaves its sign on the noncancelling quarter packet unresolved. This file
performs the NONTRIVIAL derivative-index contraction of its ordered Fourier
triad symbol, retaining all four 3+3+1 gradient contractions and all three
3+2+2 interpolation contractions.

For a test-wave frequency p, advecting-wave frequency q and transported-wave
frequency r, let a=p·q and b=p·r. The seven index-sum terms factor to

  gradient = a³ + 3 a b²,
  interpolation = 3 a² b,
  full = a(a² + 3ab + 3b²).

The quadratic factor is positive away from the simultaneous zero a=b=0.
An explicit momentum-conserving, three-component solenoidal ordered triad has
nonzero real derivative-symbol coefficient 14. This establishes that the
21-term cancellation is NOT a pointwise identity of the *ordered derivative
symbol* even on solenoidal polarizations.

IMPORTANT: this is an ordered REAL polynomial in Fourier frequencies and
polarizations. Actual Fourier derivatives introduce powers of 2πi. The
real-valued Schwartz transport is a SUM/INTEGRAL over ordered triads, their
permutations and reality-reflected partners. This module does NOT identify
the derivative symbol with that integral, or prove the FULL quarter-packet
G₃ + 3M is nonzero. That genuinely analytic phase/symmetrization task remains.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 400000

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeThirdOrderedSymbol244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Euclidean coordinate pairing on the actual positive-depth 3-axis carrier. -/
noncomputable def thirdTriadAxisDot244 (v w : A3 → ℝ) : ℝ :=
  ∑ i : A3, v i * w i

/-- One complete 3-index contraction. There are exactly 3³ ordered choices. -/
noncomputable def thirdTriadThreefold244
    (a b c : A3 → ℝ) : ℝ :=
  ∑ i : A3, ∑ k : A3, ∑ l : A3, a i * b k * c l

/-- Tensor-product separation of the three actual axis sums. -/
theorem thirdTriadThreefold_eq_prod244 (a b c : A3 → ℝ) :
    thirdTriadThreefold244 a b c =
      (∑ i : A3, a i) * (∑ k : A3, b k) * (∑ l : A3, c l) := by
  classical
  unfold thirdTriadThreefold244
  calc
    (∑ i : A3, ∑ k : A3, ∑ l : A3, a i * b k * c l) =
        ∑ i : A3, ∑ k : A3,
          (a i * b k) * (∑ l : A3, c l) := by
      simp only [Finset.mul_sum]
    _ = (∑ i : A3, ∑ k : A3, a i * b k) *
          (∑ l : A3, c l) := by
      simp only [Finset.sum_mul]
    _ = (∑ i : A3, a i) * (∑ k : A3, b k) *
          (∑ l : A3, c l) := by
      congr 1
      calc
        (∑ i : A3, ∑ k : A3, a i * b k) =
            ∑ i : A3, a i * (∑ k : A3, b k) := by
          simp only [Finset.mul_sum]
        _ = (∑ i : A3, a i) * (∑ k : A3, b k) := by
          rw [Finset.sum_mul]

/-- The FOUR 3+3+1 contractions from the original gradient commutator.
Each summand corresponds to an actual term of fullSchwartzGradientAxis244,
with the amplitude indices and the common Fourier phase factored out. -/
noncomputable def thirdGradientOrderedTriadOrders244
    (p q r : A3 → ℝ) : ℝ :=
  let a : A3 → ℝ := fun i => p i * q i
  let b : A3 → ℝ := fun i => p i * r i
  thirdTriadThreefold244 a a a +
    thirdTriadThreefold244 b b a +
      thirdTriadThreefold244 b a b +
        thirdTriadThreefold244 a b b

/-- The THREE 3+2+2 contractions from the original signed interpolation.
The factor three comes from the actual cyclic derivative expansion, not from
an independently assumed symmetry of the Fourier modes. -/
noncomputable def thirdInterpolationOrderedTriadOrders244
    (p q r : A3 → ℝ) : ℝ :=
  let a : A3 → ℝ := fun i => p i * q i
  let b : A3 → ℝ := fun i => p i * r i
  thirdTriadThreefold244 b a a +
    thirdTriadThreefold244 a b a +
      thirdTriadThreefold244 a a b

/-- Exact contraction of ALL FOUR original gradient derivative patterns. -/
theorem thirdGradientOrderedTriadOrders_eq244
    (p q r : A3 → ℝ) :
    thirdGradientOrderedTriadOrders244 p q r =
      (thirdTriadAxisDot244 p q) ^ 3 +
        3 * thirdTriadAxisDot244 p q *
          (thirdTriadAxisDot244 p r) ^ 2 := by
  unfold thirdGradientOrderedTriadOrders244
  simp only [thirdTriadThreefold_eq_prod244]
  unfold thirdTriadAxisDot244
  ring

/-- Exact contraction of all THREE intermediate derivative patterns. -/
theorem thirdInterpolationOrderedTriadOrders_eq244
    (p q r : A3 → ℝ) :
    thirdInterpolationOrderedTriadOrders244 p q r =
      3 * (thirdTriadAxisDot244 p q) ^ 2 *
        thirdTriadAxisDot244 p r := by
  unfold thirdInterpolationOrderedTriadOrders244
  simp only [thirdTriadThreefold_eq_prod244]
  unfold thirdTriadAxisDot244
  ring

/-- The ordered, contracted 21-term derivative symbol also retains the
component-amplitude contractions: (A·C)(B·r). The common physical factor 2
and the Fourier phase (2πi)^7 are deliberately NOT included here. -/
noncomputable def thirdFullOrderedTriadRealSymbol244
    (p q r A B C : A3 → ℝ) : ℝ :=
  (thirdTriadAxisDot244 A C * thirdTriadAxisDot244 B r) *
    (thirdGradientOrderedTriadOrders244 p q r +
      thirdInterpolationOrderedTriadOrders244 p q r)

/-- Exact ordered Fourier symbol factoring the common amplitudes. -/
theorem thirdFullOrderedTriadRealSymbol_eq244
    (p q r A B C : A3 → ℝ) :
    thirdFullOrderedTriadRealSymbol244 p q r A B C =
      (thirdTriadAxisDot244 A C * thirdTriadAxisDot244 B r) *
      (thirdTriadAxisDot244 p q *
        ((thirdTriadAxisDot244 p q) ^ 2 +
          3 * thirdTriadAxisDot244 p q * thirdTriadAxisDot244 p r +
          3 * (thirdTriadAxisDot244 p r) ^ 2)) := by
  unfold thirdFullOrderedTriadRealSymbol244
  rw [thirdGradientOrderedTriadOrders_eq244,
    thirdInterpolationOrderedTriadOrders_eq244]
  ring

/-- The quadratic frequency factor is positive-semidefinite for ALL real
frequencies; it cannot force algebraic gradient/interpolation cancellation. -/
theorem thirdOrderedTriadQuadratic_nonneg244 (a b : ℝ) :
    0 ≤ a ^ 2 + 3 * a * b + 3 * b ^ 2 := by
  have hs : 0 ≤ (2 * a + 3 * b) ^ 2 := sq_nonneg _
  have hb : 0 ≤ b ^ 2 := sq_nonneg _
  nlinarith

/-- On nonzero b the quadratic is strictly positive, independently of a. -/
theorem thirdOrderedTriadQuadratic_pos_of_second_ne_zero244
    (a b : ℝ) (hb : b ≠ 0) :
    0 < a ^ 2 + 3 * a * b + 3 * b ^ 2 := by
  have hs : 0 ≤ (2 * a + 3 * b) ^ 2 := sq_nonneg _
  have hb2 : 0 < b ^ 2 := by
    have hb0 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
    exact lt_of_le_of_ne (sq_nonneg b) (Ne.symm hb0)
  nlinarith

/-- The quadratic is strictly positive away from (a,b)=(0,0).
Thus there is no universal cancellation between the four gradient and three
interpolation derivative patterns at the ordered-symbol level. -/
theorem thirdOrderedTriadQuadratic_pos_of_nonzero244
    (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    0 < a ^ 2 + 3 * a * b + 3 * b ^ 2 := by
  rcases h with ha | hb
  · by_cases hb : b = 0
    · subst b
      have hA : 0 < a ^ 2 := by
        have hZero : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
        exact lt_of_le_of_ne (sq_nonneg a) (Ne.symm hZero)
      nlinarith
    · exact thirdOrderedTriadQuadratic_pos_of_second_ne_zero244 a b hb
  · exact thirdOrderedTriadQuadratic_pos_of_second_ne_zero244 a b hb

/-- Literal three-axis real frequencies and polarizations, not abstract
scalar data detached from PrimeTensor's physical axes. -/
private def thirdOrderedCoord244 (x y z : ℝ) (i : A3) : ℝ :=
  if axisRank i = 0 then x else if axisRank i = 1 then y else z

private def p244 : A3 → ℝ := thirdOrderedCoord244 1 0 0
private def q244 : A3 → ℝ := thirdOrderedCoord244 1 1 0
private def r244 : A3 → ℝ := thirdOrderedCoord244 (-2) (-1) 0
private def A244 : A3 → ℝ := thirdOrderedCoord244 0 1 0
private def B244 : A3 → ℝ := thirdOrderedCoord244 1 (-1) 0
private def C244 : A3 → ℝ := thirdOrderedCoord244 1 (-2) 0

private theorem thirdOrdered_axisDot_coordinates244
    (ax ay az bx byCoord bz : ℝ) :
    thirdTriadAxisDot244
      (thirdOrderedCoord244 ax ay az)
      (thirdOrderedCoord244 bx byCoord bz) =
        ax * bx + ay * byCoord + az * bz := by
  classical
  unfold thirdTriadAxisDot244
  rw [axis_sum_three]
  norm_num [thirdOrderedCoord244, axisRank, xAxis, yAxis, zAxis] <;> ring

/-- An explicit momentum-conserving Fourier triad with all three
polarization vectors divergence-free in their OWN wave frequencies. -/
theorem thirdOrderedSolenoidalTriad_coordinates244 :
    (∀ i : A3, p244 i + q244 i + r244 i = 0) ∧
    thirdTriadAxisDot244 A244 p244 = 0 ∧
    thirdTriadAxisDot244 B244 q244 = 0 ∧
    thirdTriadAxisDot244 C244 r244 = 0 := by
  constructor
  · intro i
    cases i with
    | first =>
        norm_num [p244, q244, r244, thirdOrderedCoord244,
          axisRank, xAxis, yAxis, zAxis]
    | next i =>
        cases i with
        | first =>
            norm_num [p244, q244, r244, thirdOrderedCoord244,
              axisRank, xAxis, yAxis, zAxis]
        | next i =>
            cases i with
            | first =>
                norm_num [p244, q244, r244, thirdOrderedCoord244,
                  axisRank, xAxis, yAxis, zAxis]
  · constructor
    · norm_num [A244, p244, thirdOrdered_axisDot_coordinates244]
    · constructor
      · norm_num [B244, q244, thirdOrdered_axisDot_coordinates244]
      · norm_num [C244, r244, thirdOrdered_axisDot_coordinates244]

/-- Here p·q=1, p·r=-2, A·C=-2, B·r=-1. Thus the fully
contracted ordered 21-term REAL derivative polynomial is exactly 14.
This does NOT assert the fully permuted, phase-correct physical integral is
nonzero. -/
theorem thirdOrderedSolenoidalTriad_nonzero_symbol244 :
    thirdFullOrderedTriadRealSymbol244 p244 q244 r244 A244 B244 C244 = 14 := by
  rw [thirdFullOrderedTriadRealSymbol_eq244]
  norm_num [p244, q244, r244, A244, B244, C244,
    thirdOrdered_axisDot_coordinates244]

end
end PrimeTensor.FirstMonomialTriad
