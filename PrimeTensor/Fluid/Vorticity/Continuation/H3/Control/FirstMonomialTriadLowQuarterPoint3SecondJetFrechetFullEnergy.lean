import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetIntegratedFrechetSquare
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualDilationEnergySums

/-!
# Full 27-slot Fréchet-square energy bounded by the genuine 81-slot E3

The integrated pointwise physical Fréchet inequality controls each ordered
second Schwartz derivative by the full three-coordinate square sum of its
third derivatives. This file sums those 27 inequalities and identifies the
result with the pre-existing 81-slot `lowNormalRealSchwartzH3Energy3`.

The triple sum on the RHS of the per-slot estimate orders the derivatives as
`a,i,k`, whereas the definition of E3 uses `i,k,l`. The proof rotates the
FINITE SUM INDICES (not the derivatives), preserving the exact Schwartz
third-derivative expressions and their multiplicities.

The factor `Fintype.card (Axis Depth.three)` records the actual product-sup
norm on Point3. There is no new analytic or PDE hypothesis.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSecondJetFrechetFullEnergy (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The complete physical L² Fréchet-square mass of all 27 ordered Schwartz
second-order derivative slots. -/
noncomputable def lowNormalRealSchwartzSecondJetPhysicalFrechetEnergy
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3,
    ∫ x : Point3,
      ‖fderiv ℝ
        (h3SchwartzPoint3Scalar
          (∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection k} (f j)))) x‖ ^ 2

/-- Rotate three *finite sums* without changing the order of the underlying
    derivatives. Keeping the rearrangement abstract prevents the elaborator
    from repeatedly reducing the full Schwartz-integral expression. -/
private theorem lowNormal_rotate_three_sums
    {J : Type*} [Fintype J] (F : J → J → J → ℝ) :
    (∑ i : J, ∑ k : J, ∑ a : J, F a i k) =
      (∑ a : J, ∑ i : J, ∑ k : J, F a i k) := by
  classical
  calc
    (∑ i : J, ∑ k : J, ∑ a : J, F a i k) =
        (∑ i : J, ∑ a : J, ∑ k : J, F a i k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The 81 ordered third-derivative masses equal E3 after a cyclic
    renaming of summation indices; mixed derivatives are not commuted. -/
theorem lowNormalRealSchwartz_thirdJet_coordinateSum_eq_E3
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ a : A3,
      ∫ ξ : V3,
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection k} (f j)))) ξ) ^ 2) =
      lowNormalRealSchwartzH3Energy3 f := by
  classical
  unfold lowNormalRealSchwartzH3Energy3
  apply Finset.sum_congr rfl
  intro j _
  -- Name the integrand before applying the *polymorphic* finite-sum lemma.
  -- This prevents elaboration of the Schwartz expressions inside sum_comm.
  let F : A3 → A3 → A3 → ℝ :=
    fun a i k =>
      ∫ ξ : V3,
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection k} (f j)))) ξ) ^ 2
  change (∑ i : A3, ∑ k : A3, ∑ a : A3, F a i k) =
    (∑ a : A3, ∑ i : A3, ∑ k : A3, F a i k)
  exact lowNormal_rotate_three_sums F

/-- Full physical Fréchet-square mass of all 27 second-order Schwartz jets
is bounded by the genuine 81-slot third-order H3 energy, with the exact
finite-coordinate factor from the physical sup norm. -/
theorem lowNormalRealSchwartz_secondJet_frechetEnergy_le_card_mul_E3
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzSecondJetPhysicalFrechetEnergy f ≤
      (Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f := by
  classical
  unfold lowNormalRealSchwartzSecondJetPhysicalFrechetEnergy
  calc
    (∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∫ x : Point3,
        ‖fderiv ℝ
          (h3SchwartzPoint3Scalar
            (∂_{h3FourierAxisDirection i}
              (∂_{h3FourierAxisDirection k} (f j)))) x‖ ^ 2) ≤
      (∑ j : A3, ∑ i : A3, ∑ k : A3,
        (Fintype.card A3 : ℝ) *
          (∑ a : A3, ∫ ξ : V3,
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection i}
                (∂_{h3FourierAxisDirection k} (f j)))) ξ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro k _
        exact lowNormalRealSchwartz_secondJet_integratedFrechet_sq_le_thirdJetMass
          f j i k
    _ = (Fintype.card A3 : ℝ) *
        (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ a : A3,
          ∫ ξ : V3,
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection i}
                (∂_{h3FourierAxisDirection k} (f j)))) ξ) ^ 2) := by
        simp only [← Finset.mul_sum]
    _ = (Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f := by
        rw [lowNormalRealSchwartz_thirdJet_coordinateSum_eq_E3]

end
end PrimeTensor.FirstMonomialTriad
