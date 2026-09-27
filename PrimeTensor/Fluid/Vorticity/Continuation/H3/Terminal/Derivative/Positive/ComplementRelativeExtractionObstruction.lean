import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeControlledExtraction

/-!
# A rate obstruction to controlled relative escape

The cofinal relative-gap extraction selects indices at which the gap exceeds
the extracted counter. A gap whose square is bounded by its original index
forces such selected indices to grow at least quadratically. Consequently
the linear index bound used to promote extracted-counter estimates to
original-index estimates is an additional rate hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Every real linear function of the counter is eventually smaller than
the square of that counter. -/
private theorem eventually_linear_lt_square (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * ((n : ℝ) + 1) < (n : ℝ) ^ 2 := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max (C + 2) 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnLarge : C + 2 < (n : ℝ) := by
    exact (lt_of_le_of_lt (le_max_left (C + 2) 1) hN).trans_le hNle
  have hnPos : 0 < (n : ℝ) := by
    have hnOne : (1 : ℝ) < (n : ℝ) :=
      (lt_of_le_of_lt (le_max_right (C + 2) 1) hN).trans_le hNle
    linarith
  have hFactor : C + 1 < (n : ℝ) := by linarith
  have hProduct :
      (n : ℝ) * (C + 1) < (n : ℝ) * (n : ℝ) :=
    mul_lt_mul_of_pos_left hFactor hnPos
  have hLinear :
      C * ((n : ℝ) + 1) ≤ (n : ℝ) * (C + 1) := by
    nlinarith
  nlinarith

/-- A slowly growing relative gap requires quadratically large indices
whenever its extracted values exceed the counter. -/
theorem relativeEscape_slowGap_forces_quadraticExtraction
    (gap : ℕ → ℝ)
    (k : ℕ → ℕ)
    (hSlow : ∀ m : ℕ, (gap m) ^ 2 ≤ (m : ℝ))
    (hEscape : ∀ n : ℕ, (n : ℝ) < gap (k n)) :
    ∀ n : ℕ, (n : ℝ) ^ 2 < (k n : ℝ) := by
  intro n
  have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hSum : 0 < gap (k n) + (n : ℝ) := by
    linarith [hEscape n]
  have hSquares :
      0 < (gap (k n) - (n : ℝ)) *
        (gap (k n) + (n : ℝ)) :=
    mul_pos (sub_pos.mpr (hEscape n)) hSum
  nlinarith [hSlow (k n)]

/-- Under the same slow-gap condition, no extraction reaching every
counter threshold can have an eventual linear upper bound. -/
theorem relativeEscape_slowGap_excludes_controlledExtraction
    (gap : ℕ → ℝ)
    (k : ℕ → ℕ)
    (hSlow : ∀ m : ℕ, (gap m) ^ 2 ≤ (m : ℝ))
    (hEscape : ∀ n : ℕ, (n : ℝ) < gap (k n))
    (C : ℝ) :
    ¬ ∀ᶠ n : ℕ in atTop,
        (k n : ℝ) ≤ C * ((n : ℝ) + 1) := by
  intro hkBound
  have hSquare :=
    relativeEscape_slowGap_forces_quadraticExtraction gap k hSlow hEscape
  obtain ⟨n, hnBound, hnGrowth⟩ :=
    (hkBound.and (eventually_linear_lt_square C)).exists
  exact (not_lt_of_ge hnBound) (hnGrowth.trans (hSquare n))

/-- In the unbounded relative-tail branch, a square-bounded gap makes the
cofinal witness incompatible with every eventual linear index bound. -/
theorem relativeTail_slowGap_requires_uncontrolledExtraction
    (gap ratio : ℕ → ℝ)
    (hEq : ∀ᶠ n : ℕ in atTop, ratio n = 1 + gap n)
    (hUnbounded :
      ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, gap n ≤ C)
    (hSlow : ∀ m : ℕ, (gap m) ^ 2 ≤ (m : ℝ)) :
    ∃ k : ℕ → ℕ,
      (∀ n : ℕ,
        n ≤ k n
          ∧
        (n : ℝ) < gap (k n)
          ∧
        (n : ℝ) + 1 < ratio (k n))
        ∧
      Tendsto k atTop atTop
        ∧
      Tendsto (fun n : ℕ => gap (k n)) atTop atTop
        ∧
      Tendsto (fun n : ℕ => ratio (k n)) atTop atTop
        ∧
      (∀ C : ℝ,
        ¬ ∀ᶠ n : ℕ in atTop,
            (k n : ℝ) ≤ C * ((n : ℝ) + 1)) := by
  rcases relativeTailAlternative_of_eventually_ratio_identity gap ratio hEq with
    ⟨C, hBound⟩ | ⟨k, hk, hkTop, hGapTop, hRatioTop⟩
  · exact False.elim
      (hUnbounded ⟨C, hBound.mono (fun n hn => hn.1)⟩)
  · refine ⟨k, hk, hkTop, hGapTop, hRatioTop, ?_⟩
    intro C
    exact relativeEscape_slowGap_excludes_controlledExtraction
      gap k hSlow (fun n => (hk n).2.1) C

end

end Euclidean
end Bridge
end PrimeTensor
