import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeExtractionObstruction

/-!
# A concrete slow-gap relative-tail witness

The square-root gap is unbounded, obeys the square bound used in the
extraction obstruction, and satisfies the exact ratio identity after
adding one. Thus the hypotheses of the rate obstruction are jointly
realizable for abstract relative-gap sequences.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem sqrt_gap_at_square_index (n : ℕ) :
    Real.sqrt ((((n + 1) ^ 2 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
  rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  exact Real.sqrt_sq (by positivity : 0 ≤ (n : ℝ) + 1)

private theorem index_le_square_index (n : ℕ) :
    n ≤ (n + 1) ^ 2 := by
  nlinarith [Nat.zero_le n]

/-- The square-root gap is not eventually bounded above. Its values on
square indices alone exceed every real threshold. -/
theorem relativeSqrtGap_not_eventually_bounded :
    ¬ ∃ C : ℝ,
      ∀ᶠ m : ℕ in atTop,
        Real.sqrt (m : ℝ) ≤ C := by
  rintro ⟨C, hBound⟩
  obtain ⟨N, hTail⟩ := eventually_atTop.1 hBound
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max C (N : ℝ))
  have hIndexCast : (N : ℝ) < (n : ℝ) :=
    (lt_of_le_of_lt (le_max_right C (N : ℝ)) hn)
  have hIndex : N ≤ (n + 1) ^ 2 := by
    have hNle : N ≤ n := by exact_mod_cast (le_of_lt hIndexCast)
    exact hNle.trans (index_le_square_index n)
  have hAtSquare := hTail ((n + 1) ^ 2) hIndex
  rw [sqrt_gap_at_square_index] at hAtSquare
  have hAbove : C < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left C (N : ℝ)) hn
  linarith

/-- The abstract tail alternative has an unbounded, square-bounded
instance. Every cofinal extraction it supplies lacks linear index
control, despite the exact ratio identity. -/
theorem relativeSqrtGap_tail_requires_uncontrolledExtraction :
    ∃ k : ℕ → ℕ,
      (∀ n : ℕ,
        n ≤ k n
          ∧
        (n : ℝ) < Real.sqrt (k n : ℝ)
          ∧
        (n : ℝ) + 1 < 1 + Real.sqrt (k n : ℝ))
        ∧
      Tendsto k atTop atTop
        ∧
      Tendsto (fun n : ℕ => Real.sqrt (k n : ℝ)) atTop atTop
        ∧
      Tendsto (fun n : ℕ => 1 + Real.sqrt (k n : ℝ)) atTop atTop
        ∧
      (∀ C : ℝ,
        ¬ ∀ᶠ n : ℕ in atTop,
            (k n : ℝ) ≤ C * ((n : ℝ) + 1)) := by
  apply relativeTail_slowGap_requires_uncontrolledExtraction
    (fun m : ℕ => Real.sqrt (m : ℝ))
    (fun m : ℕ => 1 + Real.sqrt (m : ℝ))
  · exact Filter.Eventually.of_forall (fun _ => rfl)
  · exact relativeSqrtGap_not_eventually_bounded
  · intro m
    rw [Real.sq_sqrt (Nat.cast_nonneg m)]

end

end Euclidean
end Bridge
end PrimeTensor
