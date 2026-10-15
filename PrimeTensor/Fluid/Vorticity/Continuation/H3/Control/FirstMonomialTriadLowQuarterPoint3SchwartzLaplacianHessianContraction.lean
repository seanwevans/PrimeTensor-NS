import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzMixedPairContraction

/-!
# Exact physical Schwartz Laplacian–Hessian contraction

The preceding module proves a full-space integration-by-parts contraction
for *each* pair of spatial directions. This module sums that identity rather
than bounding each diagonal slot separately. For any real Schwartz scalar F,

  ∫ (∑ᵢ ∂ᵢ²F)² = ∑ᵢ∑ₖ ∫ (∂ᵢ∂ₖF)².

In particular the complete 27-slot second H³ energy of a physical Schwartz
velocity is exactly the sum of squared componentwise Laplacians, and its
complete 81-slot third H³ energy is exactly the sum of squared Laplacians
of its first spatial jets.

These are coefficient-one identities. They do not by themselves assert the
sharp adjacent Cauchy inequalities; identifying the middle energy as the
corresponding signed lower/upper Laplacian pairing is the next step.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSchwartzHessianContraction (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual physical coordinate Laplacian of a Schwartz scalar, expressed
using the same real directional derivatives as the complete H³ energy. -/
noncomputable def lowNormalSchwartz_axisLaplacian
    (F : SchwartzMap V3 ℝ) (x : V3) : ℝ :=
  ∑ i : A3,
    ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection i} F) : SchwartzMap V3 ℝ) x)

private theorem lowNormalSchwartz_product_integrable
    (F G : SchwartzMap V3 ℝ) :
    Integrable (fun x : V3 => F x * G x) volume := by
  change Integrable (fun x : V3 =>
    (ContinuousLinearMap.lsmul ℝ ℝ) (F x) (G x)) volume
  rw [← MeasureTheory.memLp_one_iff_integrable]
  exact (ContinuousLinearMap.lsmul ℝ ℝ).memLp_of_bilin 1
    (F.memLp 2 volume) (G.memLp 2 volume)

/-- Expand the square of a finite sum of genuine real Schwartz functions
and interchange both *finite* sums with the integral. -/
private theorem lowNormalSchwartz_integral_finset_square
    (G : A3 → SchwartzMap V3 ℝ) :
    (∫ x : V3, (∑ i : A3, G i x) ^ 2) =
      ∑ i : A3, ∑ k : A3, ∫ x : V3, G i x * G k x := by
  have hProd (i k : A3) :
      Integrable (fun x : V3 => G i x * G k x) volume :=
    lowNormalSchwartz_product_integrable (G i) (G k)
  have hInner (i : A3) :
      Integrable (fun x : V3 => ∑ k : A3, G i x * G k x) volume :=
    integrable_finsetSum Finset.univ (fun k _ => hProd i k)
  calc
    (∫ x : V3, (∑ i : A3, G i x) ^ 2) =
        ∫ x : V3, ∑ i : A3, ∑ k : A3, G i x * G k x := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm
    _ = ∑ i : A3, ∑ k : A3, ∫ x : V3, G i x * G k x := by
          rw [integral_finsetSum Finset.univ (fun i _ => hInner i)]
          apply Finset.sum_congr rfl
          intro i _
          exact integral_finsetSum Finset.univ (fun k _ => hProd i k)

/-- Exact scalar Hessian–Laplacian identity, with all nine ordered direction
pairs included and with no dimension-dependent inequality constant. -/
theorem lowNormalSchwartz_axisLaplacian_sq_integral_eq_hessian
    (F : SchwartzMap V3 ℝ) :
    (∫ x : V3, (lowNormalSchwartz_axisLaplacian F x) ^ 2) =
      ∑ i : A3, ∑ k : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} F) : SchwartzMap V3 ℝ) x) ^ 2 := by
  let G : A3 → SchwartzMap V3 ℝ := fun i =>
    ∂_{h3FourierAxisDirection i} (∂_{h3FourierAxisDirection i} F)
  have hSquare := lowNormalSchwartz_integral_finset_square G
  change (∫ x : V3, (∑ i : A3, G i x) ^ 2) =
    ∑ i : A3, ∑ k : A3, ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} F) : SchwartzMap V3 ℝ) x) ^ 2
  calc
    _ = ∑ i : A3, ∑ k : A3,
      ∫ x : V3, G i x * G k x := hSquare
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact lowNormalSchwartz_secondLineDeriv_pair_eq_mixed_square
        F (h3FourierAxisDirection i) (h3FourierAxisDirection k)

/-- Exact identity between the actual complete 27-slot second H³ block
and the squared coordinate Laplacians of all three velocity components. -/
theorem lowNormalRealSchwartzH3Energy2_eq_sum_axisLaplacian_sq
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy2 f =
      ∑ j : A3, ∫ x : V3,
        (lowNormalSchwartz_axisLaplacian (f j) x) ^ 2 := by
  unfold lowNormalRealSchwartzH3Energy2
  symm
  apply Finset.sum_congr rfl
  intro j _
  exact lowNormalSchwartz_axisLaplacian_sq_integral_eq_hessian (f j)

/-- A purely finite-index rotation, independent of the large derivative
expressions to which it is applied. -/
private theorem lowNormalSchwartz_triple_sum_rotate
    {I K L : Type*} [Fintype I] [Fintype K] [Fintype L]
    (a : I → K → L → ℝ) :
    (∑ i, ∑ k, ∑ l, a i k l) =
      ∑ l, ∑ i, ∑ k, a i k l := by
  calc
    (∑ i, ∑ k, ∑ l, a i k l) =
        ∑ i, ∑ l, ∑ k, a i k l := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k, a i k l := Finset.sum_comm

/-- Exact identity between all 81 ordered third H³ derivative squares and
Laplacian squares of all nine first spatial velocity derivatives. -/
theorem lowNormalRealSchwartzH3Energy3_eq_sum_firstJet_axisLaplacian_sq
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy3 f =
      ∑ j : A3, ∑ l : A3, ∫ x : V3,
        (lowNormalSchwartz_axisLaplacian
          (∂_{h3FourierAxisDirection l} (f j)) x) ^ 2 := by
  let a : A3 → A3 → A3 → A3 → ℝ := fun j i k l =>
    ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k}
          (∂_{h3FourierAxisDirection l} (f j))) : SchwartzMap V3 ℝ) x) ^ 2
  have hRotate :
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, a j i k l) =
        ∑ j : A3, ∑ l : A3, ∑ i : A3, ∑ k : A3, a j i k l := by
    apply Finset.sum_congr rfl
    intro j _
    exact lowNormalSchwartz_triple_sum_rotate (fun i k l => a j i k l)
  have hEach (j l : A3) :
      (∑ i : A3, ∑ k : A3, a j i k l) =
        ∫ x : V3,
          (lowNormalSchwartz_axisLaplacian
            (∂_{h3FourierAxisDirection l} (f j)) x) ^ 2 := by
    exact (lowNormalSchwartz_axisLaplacian_sq_integral_eq_hessian
      (∂_{h3FourierAxisDirection l} (f j))).symm
  change (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, a j i k l) =
    ∑ j : A3, ∑ l : A3, ∫ x : V3,
      (lowNormalSchwartz_axisLaplacian
        (∂_{h3FourierAxisDirection l} (f j)) x) ^ 2
  calc
    _ = ∑ j : A3, ∑ l : A3, ∑ i : A3, ∑ k : A3, a j i k l := hRotate
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      exact hEach j l

end
end PrimeTensor.FirstMonomialTriad
