import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzAutomaticJetBounds244

/-!
# Orderwise mixed Sobolev jet graph controls all 243 signed transport slots

Instead of asking for three independent Cauchy conditions for each of the
243 five-index transport slots, consider two nonnegative scalar functionals:
the sum of all 81 third-derivative L² difference norms and the sum of all
27 second-derivative L⁴ difference norms. These are the actual real roots
of the Schwartz derivative integrals, with no formal surrogate norms.

Each 243-slot third, middle and cross derivative factor is literally one
of these 81 or 27 terms. Finite-sum positivity makes its norm at most the
single mixed graph discrepancy. Consequently, Cauchy control of one scalar
quantity implies the previous 243-slot strong-jet Cauchy condition and the
existence of a limit of the full signed Schwartz monomial.

This is an orderwise mixed L²/L⁴ *graph discrepancy*. Identifying it with
an ordinary H³/H⁴ Sobolev graph norm still requires derivative linearity,
the second-jet Gagliardo--Nirenberg estimate, and appropriate density.
The limit has not yet been identified with a non-Schwartz physical velocity.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeOrderwiseGraph244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact third-order L² derivative *difference* root. -/
noncomputable def schwartzThirdJetDifferenceRoot244
    (f g : A3 → SchwartzMap V3 ℝ) (j i k l : A3) : ℝ :=
  schwartzIntegralL2Root244
    ((∂_{h3FourierAxisDirection i}
       (∂_{h3FourierAxisDirection k}
         (∂_{h3FourierAxisDirection l} (f j)))) -
     (∂_{h3FourierAxisDirection i}
       (∂_{h3FourierAxisDirection k}
         (∂_{h3FourierAxisDirection l} (g j)))))

/-- The exact second-order L⁴ derivative *difference* root. -/
noncomputable def schwartzSecondJetDifferenceRoot244
    (f g : A3 → SchwartzMap V3 ℝ) (j i k : A3) : ℝ :=
  schwartzIntegralL4Root244
    ((∂_{h3FourierAxisDirection i}
       (∂_{h3FourierAxisDirection k} (f j))) -
     (∂_{h3FourierAxisDirection i}
       (∂_{h3FourierAxisDirection k} (g j))))

/-- All 81 third-order scalar derivative differences, each counted once. -/
noncomputable def schwartzThirdJetGraphDistance244
    (f g : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
    schwartzThirdJetDifferenceRoot244 f g j i k l

/-- All 27 second-order scalar derivative differences, each counted once. -/
noncomputable def schwartzSecondJetGraphDistance244
    (f g : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3,
    schwartzSecondJetDifferenceRoot244 f g j i k

/-- One scalar discrepancy controls both orders of genuine Lebesgue norms. -/
noncomputable def schwartzMixedJetGraphDistance244
    (f g : A3 → SchwartzMap V3 ℝ) : ℝ :=
  schwartzThirdJetGraphDistance244 f g +
    schwartzSecondJetGraphDistance244 f g

private theorem third_root_nonneg244
    (f g : A3 → SchwartzMap V3 ℝ) (j i k l : A3) :
    0 ≤ schwartzThirdJetDifferenceRoot244 f g j i k l :=
  schwartzIntegralL2Root244_nonneg _

private theorem second_root_nonneg244
    (f g : A3 → SchwartzMap V3 ℝ) (j i k : A3) :
    0 ≤ schwartzSecondJetDifferenceRoot244 f g j i k :=
  schwartzIntegralL4Root244_nonneg _

/-- The 81-term and 27-term graph contributions are nonnegative. -/
theorem schwartzMixedJetGraphDistance_nonneg244
    (f g : A3 → SchwartzMap V3 ℝ) :
    0 ≤ schwartzThirdJetGraphDistance244 f g ∧
      0 ≤ schwartzSecondJetGraphDistance244 f g ∧
      0 ≤ schwartzMixedJetGraphDistance244 f g := by
  have h3 : 0 ≤ schwartzThirdJetGraphDistance244 f g := by
    unfold schwartzThirdJetGraphDistance244
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro k _
    apply Finset.sum_nonneg
    intro l _
    exact third_root_nonneg244 f g j i k l
  have h2 : 0 ≤ schwartzSecondJetGraphDistance244 f g := by
    unfold schwartzSecondJetGraphDistance244
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro k _
    exact second_root_nonneg244 f g j i k
  exact ⟨h3, h2, add_nonneg h3 h2⟩

/-- A selected nonnegative term of a fourfold finite sum is bounded by
that sum, with no coordinate multiplicity factor. -/
private theorem fourfold_single_le_sum244
    (F : A3 → A3 → A3 → A3 → ℝ)
    (hF : ∀ j i k l, 0 ≤ F j i k l)
    (j i k l : A3) :
    F j i k l ≤ ∑ j' : A3, ∑ i' : A3, ∑ k' : A3,
      ∑ l' : A3, F j' i' k' l' := by
  classical
  have hL : F j i k l ≤ ∑ l' : A3, F j i k l' :=
    Finset.single_le_sum (fun l' _ => hF j i k l') (Finset.mem_univ l)
  have hK : (∑ l' : A3, F j i k l') ≤
      ∑ k' : A3, ∑ l' : A3, F j i k' l' := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset A3))
      (f := fun k' : A3 => ∑ l' : A3, F j i k' l')
    · intro k' _
      apply Finset.sum_nonneg
      intro l' _
      exact hF j i k' l'
    · exact Finset.mem_univ k
  have hI : (∑ k' : A3, ∑ l' : A3, F j i k' l') ≤
      ∑ i' : A3, ∑ k' : A3, ∑ l' : A3, F j i' k' l' := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset A3))
      (f := fun i' : A3 => ∑ k' : A3, ∑ l' : A3, F j i' k' l')
    · intro i' _
      apply Finset.sum_nonneg
      intro k' _
      apply Finset.sum_nonneg
      intro l' _
      exact hF j i' k' l'
    · exact Finset.mem_univ i
  have hJ : (∑ i' : A3, ∑ k' : A3, ∑ l' : A3, F j i' k' l') ≤
      ∑ j' : A3, ∑ i' : A3, ∑ k' : A3, ∑ l' : A3,
        F j' i' k' l' := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset A3))
      (f := fun j' : A3 => ∑ i' : A3, ∑ k' : A3, ∑ l' : A3, F j' i' k' l')
    · intro j' _
      apply Finset.sum_nonneg
      intro i' _
      apply Finset.sum_nonneg
      intro k' _
      apply Finset.sum_nonneg
      intro l' _
      exact hF j' i' k' l'
    · exact Finset.mem_univ j
  exact (hL.trans hK).trans (hI.trans hJ)

/-- The same selection bound for a threefold sum. -/
private theorem threefold_single_le_sum244
    (F : A3 → A3 → A3 → ℝ)
    (hF : ∀ j i k, 0 ≤ F j i k)
    (j i k : A3) :
    F j i k ≤ ∑ j' : A3, ∑ i' : A3, ∑ k' : A3,
      F j' i' k' := by
  classical
  have hK : F j i k ≤ ∑ k' : A3, F j i k' :=
    Finset.single_le_sum (fun k' _ => hF j i k') (Finset.mem_univ k)
  have hI : (∑ k' : A3, F j i k') ≤
      ∑ i' : A3, ∑ k' : A3, F j i' k' := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset A3))
      (f := fun i' : A3 => ∑ k' : A3, F j i' k')
    · intro i' _
      apply Finset.sum_nonneg
      intro k' _
      exact hF j i' k'
    · exact Finset.mem_univ i
  have hJ : (∑ i' : A3, ∑ k' : A3, F j i' k') ≤
      ∑ j' : A3, ∑ i' : A3, ∑ k' : A3, F j' i' k' := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset A3))
      (f := fun j' : A3 => ∑ i' : A3, ∑ k' : A3, F j' i' k')
    · intro j' _
      apply Finset.sum_nonneg
      intro i' _
      apply Finset.sum_nonneg
      intro k' _
      exact hF j' i' k'
    · exact Finset.mem_univ j
  exact (hK.trans hI).trans hJ

/-- Each of the three factors of every signed 243-slot perturbation is
bounded by one orderwise mixed L²/L⁴ graph discrepancy. -/
theorem schwartzMixedJetGraphDistance_bounds_slots244
    (f g : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) :
    schwartzThirdJetDifferenceRoot244 f g
        p.2.2.2.2 p.1 p.2.1 p.2.2.1 ≤
      schwartzMixedJetGraphDistance244 f g ∧
    schwartzSecondJetDifferenceRoot244 f g
        p.2.2.2.1 p.2.1 p.2.2.1 ≤
      schwartzMixedJetGraphDistance244 f g ∧
    schwartzSecondJetDifferenceRoot244 f g
        p.2.2.2.2 p.1 p.2.2.2.1 ≤
      schwartzMixedJetGraphDistance244 f g := by
  have hNonneg := schwartzMixedJetGraphDistance_nonneg244 f g
  have hThird (j i k l : A3) :
      schwartzThirdJetDifferenceRoot244 f g j i k l ≤
        schwartzMixedJetGraphDistance244 f g := by
    calc
      _ ≤ schwartzThirdJetGraphDistance244 f g := by
        unfold schwartzThirdJetGraphDistance244
        exact fourfold_single_le_sum244
          (schwartzThirdJetDifferenceRoot244 f g)
          (third_root_nonneg244 f g) j i k l
      _ ≤ schwartzMixedJetGraphDistance244 f g := by
        unfold schwartzMixedJetGraphDistance244
        exact le_add_of_nonneg_right hNonneg.2.1
  have hSecond (j i k : A3) :
      schwartzSecondJetDifferenceRoot244 f g j i k ≤
        schwartzMixedJetGraphDistance244 f g := by
    calc
      _ ≤ schwartzSecondJetGraphDistance244 f g := by
        unfold schwartzSecondJetGraphDistance244
        exact threefold_single_le_sum244
          (schwartzSecondJetDifferenceRoot244 f g)
          (second_root_nonneg244 f g) j i k
      _ ≤ schwartzMixedJetGraphDistance244 f g := by
        unfold schwartzMixedJetGraphDistance244
        exact le_add_of_nonneg_left hNonneg.1
  exact ⟨hThird _ _ _ _, hSecond _ _ _, hSecond _ _ _⟩

/-- One scalar Cauchy condition on a mixed derivative graph, not 243
independent five-coordinate conditions. -/
def SchwartzMixedJetGraphCauchy244
    (f : ℕ → A3 → SchwartzMap V3 ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
      schwartzMixedJetGraphDistance244 (f m) (f n) < δ

/-- Orderwise graph Cauchy control discharges every original 243-slot
third-L²/middle-L⁴/cross-L⁴ strong Cauchy condition. -/
theorem SchwartzMixedJetGraphCauchy244.toStrongJets
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    (hGraph : SchwartzMixedJetGraphCauchy244 f) :
    Schwartz243StrongJetCauchy244 f := by
  intro p δ hδ
  obtain ⟨N, hN⟩ := hGraph δ hδ
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hUpper := hN m hm n hn
  have hBounds := schwartzMixedJetGraphDistance_bounds_slots244 (f m) (f n) p
  change
    schwartzThirdJetDifferenceRoot244 (f m) (f n)
        p.2.2.2.2 p.1 p.2.1 p.2.2.1 < δ ∧
    schwartzSecondJetDifferenceRoot244 (f m) (f n)
        p.2.2.2.1 p.2.1 p.2.2.1 < δ ∧
    schwartzSecondJetDifferenceRoot244 (f m) (f n)
        p.2.2.2.2 p.1 p.2.2.2.1 < δ
  exact ⟨lt_of_le_of_lt hBounds.1 hUpper,
    lt_of_le_of_lt hBounds.2.1 hUpper,
    lt_of_le_of_lt hBounds.2.2 hUpper⟩

/-- The complete signed 243-slot first monomial has a real limit whenever
one orderwise L²/L⁴ graph discrepancy is Cauchy on late approximants. -/
theorem lowNormalRealSchwartz_firstMonomial_existsLimit_of_mixedJetGraph244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hGraph : SchwartzMixedJetGraphCauchy244 f) :
    ∃ M : ℝ,
      Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (f n))
        atTop (𝓝 M) :=
  lowNormalRealSchwartz_firstMonomial_existsLimit_of_strongJetCauchy244
    f hGraph.toStrongJets

end
end PrimeTensor.FirstMonomialTriad
