import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzLaplacianHessianContraction

/-!
# Exact signed Laplacian pairings for actual physical Schwartz H3 energies

The Laplacian/Hessian contraction in the preceding file identifies the
complete 27- and 81-slot energies with genuine componentwise Laplacian
squares. Here finite sums of the established real-Schwartz integration by
parts identity give signed pairings

  E1 = - sum_j <f_j, Delta f_j>,
  E2 = - sum_{j,k} <d_k f_j, Delta d_k f_j>.

The coefficient-one adjacent Cauchy inequalities are established in the
subsequent module after applying finite-family Cauchy to these pairings.

No Fourier conversion, PDE assumption, solenoidal hypothesis or additional
interpolation condition is used. The full ordered Schwartz energy blocks
retain their existing definitions.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSharpAdjacent (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The axis Laplacian is itself a real Schwartz function. -/
noncomputable def lowNormalSchwartz_axisLaplacianMap
    (F : SchwartzMap V3 ℝ) : SchwartzMap V3 ℝ :=
  ∑ i : A3,
    ∂_{h3FourierAxisDirection i} (∂_{h3FourierAxisDirection i} F)

@[simp] theorem lowNormalSchwartz_axisLaplacianMap_apply
    (F : SchwartzMap V3 ℝ) (x : V3) :
    lowNormalSchwartz_axisLaplacianMap F x =
      lowNormalSchwartz_axisLaplacian F x := by
  classical
  simp only [lowNormalSchwartz_axisLaplacianMap,
    lowNormalSchwartz_axisLaplacian, sum_apply]

/-- The sum of first-derivative squares is exactly the negative
lower/Laplacian pairing. No boundary term is present for Schwartz data. -/
theorem lowNormalSchwartz_firstSquares_eq_neg_laplacian_pair
    (F : SchwartzMap V3 ℝ) :
    (∑ i : A3, ∫ x : V3,
      ((∂_{h3FourierAxisDirection i} F : SchwartzMap V3 ℝ) x) ^ 2) =
      -(∫ x : V3, F x * lowNormalSchwartz_axisLaplacianMap F x) := by
  have hInt (i : A3) :
      Integrable (fun x : V3 => F x *
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection i} F) : SchwartzMap V3 ℝ) x)) volume := by
    change Integrable (fun x : V3 =>
      (ContinuousLinearMap.lsmul ℝ ℝ) (F x)
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection i} F) : SchwartzMap V3 ℝ) x)) volume
    rw [← MeasureTheory.memLp_one_iff_integrable]
    exact (ContinuousLinearMap.lsmul ℝ ℝ).memLp_of_bilin 1
      (F.memLp 2 volume)
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection i} F) : SchwartzMap V3 ℝ).memLp 2 volume)
  calc
    _ = ∑ i : A3, -(∫ x : V3, F x *
          ((∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection i} F) : SchwartzMap V3 ℝ) x)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact lowNormalSchwartz_lineDeriv_square_by_parts F
          (h3FourierAxisDirection i)
    _ = -(∫ x : V3, ∑ i : A3, F x *
          ((∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection i} F) : SchwartzMap V3 ℝ) x)) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        exact (integral_finsetSum Finset.univ (fun i _ => hInt i)).symm
    _ = -(∫ x : V3, F x * lowNormalSchwartz_axisLaplacianMap F x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        -- Expand the named Laplacian before distributing multiplication.
        -- `Finset.mul_sum` cannot match the opaque `axisLaplacian` wrapper.
        simp only [lowNormalSchwartz_axisLaplacianMap_apply,
          lowNormalSchwartz_axisLaplacian, Finset.mul_sum]

/-- All nine first-order physical slots give the signed zeroth/Laplacian
pairing, summed across the three genuine velocity components. -/
theorem lowNormalRealSchwartzH3Energy1_eq_neg_sum_laplacian_pair
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy1 f =
      -(∑ j : A3, ∫ x : V3,
        f j x * lowNormalSchwartz_axisLaplacianMap (f j) x) := by
  unfold lowNormalRealSchwartzH3Energy1
  calc
    _ = ∑ j : A3, -(∫ x : V3,
          f j x * lowNormalSchwartz_axisLaplacianMap (f j) x) := by
        apply Finset.sum_congr rfl
        intro j _
        exact lowNormalSchwartz_firstSquares_eq_neg_laplacian_pair (f j)
    _ = _ := by rw [Finset.sum_neg_distrib]

/-- All 27 second-order slots give the signed first-jet/Laplacian pairing.
The finite-axis interchange is isolated from the actual derivatives. -/
theorem lowNormalRealSchwartzH3Energy2_eq_neg_firstJet_laplacian_pair
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy2 f =
      -(∑ j : A3, ∑ k : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection k} (f j) : SchwartzMap V3 ℝ) x) *
          lowNormalSchwartz_axisLaplacianMap
            (∂_{h3FourierAxisDirection k} (f j)) x) := by
  let a : A3 → A3 → A3 → ℝ := fun j i k =>
    ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j)) : SchwartzMap V3 ℝ) x) ^ 2
  have hRotate :
      (∑ j : A3, ∑ i : A3, ∑ k : A3, a j i k) =
        ∑ j : A3, ∑ k : A3, ∑ i : A3, a j i k := by
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_comm
  have hEach (j k : A3) :
      (∑ i : A3, a j i k) =
        -(∫ x : V3,
          ((∂_{h3FourierAxisDirection k} (f j) : SchwartzMap V3 ℝ) x) *
            lowNormalSchwartz_axisLaplacianMap
              (∂_{h3FourierAxisDirection k} (f j)) x) :=
    lowNormalSchwartz_firstSquares_eq_neg_laplacian_pair
      (∂_{h3FourierAxisDirection k} (f j))
  change (∑ j : A3, ∑ i : A3, ∑ k : A3, a j i k) =
    -(∑ j : A3, ∑ k : A3, ∫ x : V3,
      ((∂_{h3FourierAxisDirection k} (f j) : SchwartzMap V3 ℝ) x) *
        lowNormalSchwartz_axisLaplacianMap
          (∂_{h3FourierAxisDirection k} (f j)) x)
  calc
    _ = ∑ j : A3, ∑ k : A3, ∑ i : A3, a j i k := hRotate
    _ = ∑ j : A3, ∑ k : A3, -(∫ x : V3,
          ((∂_{h3FourierAxisDirection k} (f j) : SchwartzMap V3 ℝ) x) *
            lowNormalSchwartz_axisLaplacianMap
              (∂_{h3FourierAxisDirection k} (f j)) x) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        exact hEach j k
    _ = _ := by simp only [Finset.sum_neg_distrib]

end
end PrimeTensor.FirstMonomialTriad
