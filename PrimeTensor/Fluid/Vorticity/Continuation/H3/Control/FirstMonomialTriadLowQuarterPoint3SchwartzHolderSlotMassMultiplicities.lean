import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetQuarticGN
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzExactHolder244

/-!
# Exact 243-slot multiplicities in first-monomial 2-4-4 Holder

The actual signed first monomial has ordered indices (i,k,l,r,j).
Its third-order factor is D_i D_k D_l f_j; its two second-order
factors are D_k D_l f_r and D_i D_r f_j.

Summing their respective *squared* / *fourth-power* integrals across the
243 slots yields, without commuting derivatives or discarding indices:

  third factor: card(Axis three) * E3
  first second factor: card(Axis three)^2 * Q4
  second second factor: card(Axis three)^2 * Q4

Here E3 is the established 81-slot third-order Schwartz energy, and Q4
is the genuine 27-slot second-derivative quartic mass from quartic GN.
These are the precise discrete multiplicities needed to transfer the
existing signed 2-4-4 Holder estimate to global energy quantities.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeFirstMonomialSlotMass (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-! The reindexing lemmas are polymorphic in the finite index type so Lean
never unfolds an integral or Schwartz derivative during sum_comm. -/

private theorem firstMonomial_rotate_three
    {J : Type*} [Fintype J] (F : J → J → J → ℝ) :
    (∑ a : J, ∑ b : J, ∑ c : J, F a b c) =
      ∑ c : J, ∑ a : J, ∑ b : J, F a b c := by
  classical
  calc
    _ = ∑ a : J, ∑ c : J, ∑ b : J, F a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem firstMonomial_rotate_four
    {J : Type*} [Fintype J] (F : J → J → J → J → ℝ) :
    (∑ i : J, ∑ k : J, ∑ l : J, ∑ j : J, F i k l j) =
      ∑ j : J, ∑ i : J, ∑ k : J, ∑ l : J, F i k l j := by
  classical
  calc
    _ = ∑ i : J, ∑ k : J, ∑ j : J, ∑ l : J, F i k l j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ i : J, ∑ j : J, ∑ k : J, ∑ l : J, F i k l j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The third-order factor has precisely one free index among the five
ordered first-monomial indices. -/
private theorem firstMonomial_five_third_factor
    {J : Type*} [Fintype J] (F : J → J → J → J → ℝ) :
    (∑ i : J, ∑ k : J, ∑ l : J, ∑ r : J, ∑ j : J, F i k l j) =
      (Fintype.card J : ℝ) *
        (∑ j : J, ∑ i : J, ∑ k : J, ∑ l : J, F i k l j) := by
  classical
  have hR (i k l : J) :
      (∑ r : J, ∑ j : J, F i k l j) =
        (Fintype.card J : ℝ) * (∑ j : J, F i k l j) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ = (∑ i : J, ∑ k : J, ∑ l : J,
          (Fintype.card J : ℝ) * (∑ j : J, F i k l j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      exact hR i k l
    _ = (Fintype.card J : ℝ) *
          (∑ i : J, ∑ k : J, ∑ l : J, ∑ j : J, F i k l j) := by
      simp only [← Finset.mul_sum]
    _ = _ := by rw [firstMonomial_rotate_four F]

/-- The middle factor is independent of the first and last indices:
its 243-slot fourth-power mass is card^2 times the 27-slot mass. -/
private theorem firstMonomial_five_middle_factor
    {J : Type*} [Fintype J] (B : J → J → J → ℝ) :
    (∑ i : J, ∑ k : J, ∑ l : J, ∑ r : J, ∑ j : J, B k l r) =
      (Fintype.card J : ℝ) ^ 2 *
        (∑ r : J, ∑ k : J, ∑ l : J, B k l r) := by
  classical
  have hJ (k l r : J) :
      (∑ j : J, B k l r) = (Fintype.card J : ℝ) * B k l r := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ = (∑ i : J, ∑ k : J, ∑ l : J, ∑ r : J,
          (Fintype.card J : ℝ) * B k l r) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro r _
      exact hJ k l r
    _ = (Fintype.card J : ℝ) *
          (∑ i : J, ∑ k : J, ∑ l : J, ∑ r : J, B k l r) := by
      simp only [← Finset.mul_sum]
    _ = (Fintype.card J : ℝ) *
          ((Fintype.card J : ℝ) *
            (∑ k : J, ∑ l : J, ∑ r : J, B k l r)) := by
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by
      rw [firstMonomial_rotate_three B]
      ring

/-- The cross factor is independent of the two middle derivative indices. -/
private theorem firstMonomial_five_cross_factor
    {J : Type*} [Fintype J] (C : J → J → J → ℝ) :
    (∑ i : J, ∑ k : J, ∑ l : J, ∑ r : J, ∑ j : J, C i r j) =
      (Fintype.card J : ℝ) ^ 2 *
        (∑ j : J, ∑ i : J, ∑ r : J, C i r j) := by
  classical
  have hL (i : J) :
      (∑ l : J, ∑ r : J, ∑ j : J, C i r j) =
        (Fintype.card J : ℝ) * (∑ r : J, ∑ j : J, C i r j) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ = (∑ i : J, ∑ k : J,
          (Fintype.card J : ℝ) * (∑ r : J, ∑ j : J, C i r j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact hL i
    _ = (Fintype.card J : ℝ) *
          (∑ i : J, ∑ k : J, ∑ r : J, ∑ j : J, C i r j) := by
      simp only [← Finset.mul_sum]
    _ = (Fintype.card J : ℝ) *
          ((Fintype.card J : ℝ) *
            (∑ i : J, ∑ r : J, ∑ j : J, C i r j)) := by
      congr 1
      -- One additional finite sum surrounds the constant-weighted terms.
      -- Pull the common cardinality factor outside this outer sum too.
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum]
    _ = _ := by
      rw [firstMonomial_rotate_three C]
      ring

/-! The following masses use EXACTLY the original five first-monomial
indices (i,k,l,r,j) and the actual real Schwartz derivatives. -/

/-- Third factor, squared, in all 243 signed first-monomial slots. -/
noncomputable def lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
    ∫ ξ : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k}
          (∂_{h3FourierAxisDirection l} (f j)))) ξ) ^ 2

/-- First second-jet factor, fourth-power, across all 243 slots. -/
noncomputable def lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
    ∫ ξ : V3,
      ((∂_{h3FourierAxisDirection k}
        (∂_{h3FourierAxisDirection l} (f r))) ξ) ^ 4

/-- Second second-jet factor, fourth-power, across all 243 slots. -/
noncomputable def lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
    ∫ ξ : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection r} (f j))) ξ) ^ 4

/-- Third-factor L² mass counts the genuine 81 third-jet terms exactly
three times (one repetition for the unused velocity index r). -/
theorem lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass_eq_card_mul_E3
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass f =
      (Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f := by
  classical
  let F : A3 → A3 → A3 → A3 → ℝ := fun i k l j =>
    ∫ ξ : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k}
          (∂_{h3FourierAxisDirection l} (f j)))) ξ) ^ 2
  change (∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3, F i k l j) =
    (Fintype.card A3 : ℝ) *
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, F i k l j)
  exact firstMonomial_five_third_factor F

/-- The first second-jet factor has exactly 9 copies of the complete
27-slot quartic mass; both unused indices are summed, not dropped. -/
theorem lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass_eq_card_sq_mul_Q4
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass f =
      (Fintype.card A3 : ℝ) ^ 2 *
        lowNormalRealSchwartzSecondJetsQuarticMass f := by
  classical
  let B : A3 → A3 → A3 → ℝ := fun k l r =>
    ∫ ξ : V3,
      ((∂_{h3FourierAxisDirection k}
        (∂_{h3FourierAxisDirection l} (f r))) ξ) ^ 4
  change (∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3, B k l r) =
    (Fintype.card A3 : ℝ) ^ 2 *
      (∑ r : A3, ∑ k : A3, ∑ l : A3, B k l r)
  exact firstMonomial_five_middle_factor B

/-- The cross second-jet factor also contributes exactly 9 copies of the
same 27-slot quartic mass, again with no derivative commutation. -/
theorem lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass_eq_card_sq_mul_Q4
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass f =
      (Fintype.card A3 : ℝ) ^ 2 *
        lowNormalRealSchwartzSecondJetsQuarticMass f := by
  classical
  let C : A3 → A3 → A3 → ℝ := fun i r j =>
    ∫ ξ : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection r} (f j))) ξ) ^ 4
  change (∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3, C i r j) =
    (Fintype.card A3 : ℝ) ^ 2 *
      (∑ j : A3, ∑ i : A3, ∑ r : A3, C i r j)
  exact firstMonomial_five_cross_factor C


/-- The exact fourth-power moment product appearing after discrete 2-4-4
Holder has coefficient card(Axis three)^6. It is a genuine 243-slot identity,
not yet an inequality for the signed monomial itself. -/
theorem lowNormalRealSchwartz_firstMonomialSlotMomentProduct_eq_E3_Q4
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass f) ^ 2 *
      (lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass f *
        lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass f) =
      (Fintype.card A3 : ℝ) ^ 6 *
        ((lowNormalRealSchwartzH3Energy3 f) ^ 2 *
          (lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2) := by
  rw [lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass_eq_card_mul_E3,
    lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass_eq_card_sq_mul_Q4,
    lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass_eq_card_sq_mul_Q4]
  ring

end
end PrimeTensor.FirstMonomialTriad
