import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3ComplexLerayWiener
import Mathlib.Tactic

/-!
# Genuine Z3 complex Leray convolution, including Galerkin output collisions

The previous module proved the complex Euclidean orthogonal Leray projection
bound and a Z3 ordered source estimate conditional on the lattice frequency
comparison. Here the frequency comparison is proved from the Euclidean norm
square and the existing all-finite-set square-sum estimate.

We then form the actual complex quadratic Fourier coefficient at each output
mode by summing *all ordered input pairs* with p+q=n. For an arbitrary finite
output set, the complete weighted sum of output coefficient norms is bounded
by W_r(u) D_r(v), with constant one and no support/cardinality factor.
This includes interactions whose output is absent from both input supports,
and allows many distinct ordered pairs to land at the same frequency.

The derivative in time of the weighted Galerkin norm, the Laplacian sign
at a zero Fourier coefficient, and the infinite-dimensional limit are
separate obligations. This file does not assert a PDE solution or a terminal
continuation theorem and does not alter the intrinsic prime-multiset carrier.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

private abbrev ComplexZ3Band244 := EuclideanSpace ℂ (Fin 3)

/-- The true Euclidean frequency norm never exceeds the integer Z3 l1 degree.
No assumption on frequency or finite support is needed. -/
theorem thirdFullThreeBand_z3ComplexFrequency_norm_le_degree244
    (q : thirdFullThreeBandZ3Index244) :
    ‖thirdFullThreeBandZ3ComplexFrequency244 q‖ ≤
      thirdFullThreeBandZ3Degree244 q := by
  have hcoord (j : Fin 3) :
      ‖(thirdFullThreeBandZ3ComplexFrequency244 q).ofLp j‖ =
        |(q j : ℝ)| := by
    change ‖(q j : ℂ)‖ = |(q j : ℝ)|
    simp
  have hsq :
      ‖thirdFullThreeBandZ3ComplexFrequency244 q‖ ^ 2 ≤
        (thirdFullThreeBandZ3Degree244 q) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      (∑ j : Fin 3,
          ‖(thirdFullThreeBandZ3ComplexFrequency244 q).ofLp j‖ ^ 2) =
          ∑ j : Fin 3, |(q j : ℝ)| ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hcoord j]
      _ ≤ (∑ j : Fin 3, |(q j : ℝ)|) ^ 2 := by
        exact thirdFullThreeBand_finiteSquares_le_squareSum244
          Finset.univ (fun j : Fin 3 => |(q j : ℝ)|)
          (fun j => abs_nonneg _)
      _ = (thirdFullThreeBandZ3Degree244 q) ^ 2 := rfl
  have hn := norm_nonneg (thirdFullThreeBandZ3ComplexFrequency244 q)
  have hd := thirdFullThreeBand_z3Degree_nonneg244 q
  nlinarith

/-- The exact full complex ordered-source estimate, now unconditional. -/
theorem thirdFullThreeBand_z3ComplexOrderedWiener_unconditional244
    (r : ℝ) (hr : 0 ≤ r)
    (s t : Finset thirdFullThreeBandZ3Index244)
    (u v : thirdFullThreeBandZ3Index244 → ComplexZ3Band244) :
    (∑ p ∈ s, ∑ q ∈ t,
      thirdFullThreeBandZ3Weight244 r (p + q) *
        ‖thirdFullThreeBandZ3ComplexTransport244 (p + q) q (u p) (v q)‖) ≤
      (∑ p ∈ s, thirdFullThreeBandZ3Weight244 r p * ‖u p‖) *
      (∑ q ∈ t, thirdFullThreeBandZ3Weight244 r q *
        thirdFullThreeBandZ3Degree244 q * ‖v q‖) := by
  apply thirdFullThreeBand_z3ComplexOrderedWienerBound244 r hr s t u v
  intro q hq
  exact thirdFullThreeBand_z3ComplexFrequency_norm_le_degree244 q

/-- Finite Galerkin quadratic Fourier coefficient, for arbitrary input sets.
The Leray projector is taken at the actual output mode n. No assumption
of six-mode closure is made. -/
def thirdFullThreeBandZ3GalerkinQuadratic244
    (s t : Finset thirdFullThreeBandZ3Index244)
    (u v : thirdFullThreeBandZ3Index244 → ComplexZ3Band244)
    (n : thirdFullThreeBandZ3Index244) : ComplexZ3Band244 :=
  ∑ p ∈ s, ∑ q ∈ t,
    if p + q = n then
      thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)
    else 0

/-- The full quadratic coefficient is bounded by the sum of its ordered
pair norms, including colliding output frequencies. -/
theorem thirdFullThreeBand_z3GalerkinQuadratic_norm_le244
    (s t : Finset thirdFullThreeBandZ3Index244)
    (u v : thirdFullThreeBandZ3Index244 → ComplexZ3Band244)
    (n : thirdFullThreeBandZ3Index244) :
    ‖thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n‖ ≤
      ∑ p ∈ s, ∑ q ∈ t,
        if p + q = n then
          ‖thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)‖
        else 0 := by
  unfold thirdFullThreeBandZ3GalerkinQuadratic244
  calc
    _ ≤ ∑ p ∈ s,
        ‖∑ q ∈ t,
          if p + q = n then
            thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)
          else 0‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ s, ∑ q ∈ t,
        ‖if p + q = n then
          thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)
        else 0‖ := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> simp

/-- A *complete arbitrary output set* of projected Fourier coefficients is
bounded by a single W_r D_r product. Crucially there is no multiplier
proportional to the number of output frequencies or the number of colliding
ordered pairs: the output equality is counted once per input pair. -/
theorem thirdFullThreeBand_z3GalerkinAllOutputWienerBound244
    (r : ℝ) (hr : 0 ≤ r)
    (outputs s t : Finset thirdFullThreeBandZ3Index244)
    (u v : thirdFullThreeBandZ3Index244 → ComplexZ3Band244) :
    (∑ n ∈ outputs, thirdFullThreeBandZ3Weight244 r n *
      ‖thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n‖) ≤
      (∑ p ∈ s, thirdFullThreeBandZ3Weight244 r p * ‖u p‖) *
      (∑ q ∈ t, thirdFullThreeBandZ3Weight244 r q *
        thirdFullThreeBandZ3Degree244 q * ‖v q‖) := by
  classical
  have hweighted (n : thirdFullThreeBandZ3Index244) :
      thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n‖ ≤
      ∑ p ∈ s, ∑ q ∈ t,
        if p + q = n then
          thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)‖
        else 0 := by
    have h := mul_le_mul_of_nonneg_left
      (thirdFullThreeBand_z3GalerkinQuadratic_norm_le244 s t u v n)
      (thirdFullThreeBand_z3Weight_pos244 r n).le
    calc
      _ ≤ thirdFullThreeBandZ3Weight244 r n *
          (∑ p ∈ s, ∑ q ∈ t,
            if p + q = n then
              ‖thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)‖
            else 0) := h
      _ = _ := by
        simp only [Finset.mul_sum, mul_ite, mul_zero]
  have hsingle (p q : thirdFullThreeBandZ3Index244) :
      (∑ n ∈ outputs,
        if p + q = n then
          thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)‖
        else 0) ≤
      thirdFullThreeBandZ3Weight244 r (p + q) *
        ‖thirdFullThreeBandZ3ComplexTransport244 (p + q) q (u p) (v q)‖ := by
    rw [Finset.sum_ite_eq]
    by_cases hm : p + q ∈ outputs
    · simp [hm]
    · have hnonneg : 0 ≤ thirdFullThreeBandZ3Weight244 r (p + q) *
          ‖thirdFullThreeBandZ3ComplexTransport244 (p + q) q (u p) (v q)‖ :=
        mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r (p + q)).le
          (norm_nonneg _)
      simpa [hm] using hnonneg
  calc
    _ ≤ ∑ n ∈ outputs, ∑ p ∈ s, ∑ q ∈ t,
          if p + q = n then
            thirdFullThreeBandZ3Weight244 r n *
              ‖thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)‖
          else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      exact hweighted n
    _ = ∑ p ∈ s, ∑ q ∈ t, ∑ n ∈ outputs,
          if p + q = n then
            thirdFullThreeBandZ3Weight244 r n *
              ‖thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)‖
          else 0 := by
      calc
        _ = ∑ p ∈ s, ∑ n ∈ outputs, ∑ q ∈ t,
              if p + q = n then
                thirdFullThreeBandZ3Weight244 r n *
                  ‖thirdFullThreeBandZ3ComplexTransport244 n q (u p) (v q)‖
              else 0 := by rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ s, ∑ q ∈ t,
        thirdFullThreeBandZ3Weight244 r (p + q) *
          ‖thirdFullThreeBandZ3ComplexTransport244 (p + q) q (u p) (v q)‖ := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact hsingle p q
    _ ≤ _ := thirdFullThreeBand_z3ComplexOrderedWiener_unconditional244
      r hr s t u v

end
end PrimeTensor.FirstMonomialTriad
