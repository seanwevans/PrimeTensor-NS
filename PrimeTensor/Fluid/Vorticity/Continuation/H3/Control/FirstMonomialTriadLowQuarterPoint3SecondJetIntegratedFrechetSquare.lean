import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetFrechetCoordinateSquare
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Closure
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrating the second-jet Frechet-coordinate square inequality

The pointwise inequality already established by the preceding module reads

  ‖Dg(x)‖² ≤ card(Axis three) * ∑ a, (∂ₐg(x))².

For L² first derivatives, both sides are integrable. Bochner integral
monotonicity, linearity of finite sums, and uniform coordinate transport give
an unconditional corresponding estimate for each of the genuine ordered
second-order Schwartz jets of the physical first-monomial family.

The factor card(Axis three) is intentional: the physical carrier uses the
sup norm. The complete 27-slot reindexing to E3 is a subsequent theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv ENNReal

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSecondJetIntegratedSquare (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Integrate the complete pointwise square comparison for any C¹ field
whose Fréchet and three coordinate derivatives belong to L². -/
theorem lowNormalPoint3_fderiv_integral_sq_le_card_mul_partials
    (g : ScalarField3) (hC1 : SpatialC1 g)
    (hD : MemLp (fun x : Point3 => fderiv ℝ g x)
      (2 : ℝ≥0∞) (volume : Measure Point3))
    (hPart : ∀ a : A3,
      MemLp (spatial3.d a g) (2 : ℝ≥0∞) (volume : Measure Point3)) :
    (∫ x : Point3, ‖fderiv ℝ g x‖ ^ 2) ≤
      (Fintype.card A3 : ℝ) *
        (∑ a : A3, ∫ x : Point3, ((spatial3.d a g) x) ^ 2) := by
  classical
  have hDInt :
      Integrable (fun x : Point3 => ‖fderiv ℝ g x‖ ^ 2)
        (volume : Measure Point3) :=
    hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hPartInt (a : A3) :
      Integrable (fun x : Point3 => ((spatial3.d a g) x) ^ 2)
        (volume : Measure Point3) :=
    (hPart a).integrable_sq
  have hSumInt :
      Integrable (fun x : Point3 =>
        ∑ a : A3, ((spatial3.d a g) x) ^ 2)
        (volume : Measure Point3) := by
    exact integrable_finsetSum (Finset.univ : Finset A3) (by
      intro a ha
      exact hPartInt a)
  have hRightInt :
      Integrable (fun x : Point3 =>
        (Fintype.card A3 : ℝ) *
          ∑ a : A3, ((spatial3.d a g) x) ^ 2)
        (volume : Measure Point3) :=
    hSumInt.const_mul _
  have hMonotone :
      (∫ x : Point3, ‖fderiv ℝ g x‖ ^ 2) ≤
        ∫ x : Point3, (Fintype.card A3 : ℝ) *
          ∑ a : A3, ((spatial3.d a g) x) ^ 2 := by
    exact integral_mono_ae hDInt hRightInt
      (Filter.Eventually.of_forall fun x =>
        lowNormalPoint3_fderiv_sq_le_card_mul_partial_sq g hC1 x)
  calc
    (∫ x : Point3, ‖fderiv ℝ g x‖ ^ 2) ≤
        ∫ x : Point3, (Fintype.card A3 : ℝ) *
          ∑ a : A3, ((spatial3.d a g) x) ^ 2 := hMonotone
    _ = (Fintype.card A3 : ℝ) *
          (∑ a : A3, ∫ x : Point3, ((spatial3.d a g) x) ^ 2) := by
      rw [integral_const_mul]
      congr 1
      exact integral_finsetSum (Finset.univ : Finset A3)
        (by intro a ha; exact hPartInt a)

/-- Every real Schwartz field pulled back to Point3 has an integrated
Frechet-square bound by the EXACT integral squares of its Euclidean
coordinate derivatives, with the genuine finite-dimensional factor. -/
theorem lowNormalSchwartz_integral_physicalFrechet_sq_le_coordinateMass
    (G : SchwartzMap V3 ℝ) :
    (∫ x : Point3,
      ‖fderiv ℝ (h3SchwartzPoint3Scalar G) x‖ ^ 2) ≤
      (Fintype.card A3 : ℝ) *
        (∑ a : A3, ∫ ξ : V3,
          ((∂_{h3FourierAxisDirection a} G) ξ) ^ 2) := by
  classical
  have hC1 : SpatialC1 (h3SchwartzPoint3Scalar G) := by
    change ContDiff ℝ 1 (h3SchwartzPoint3Scalar G)
    rw [← lowNormalSchwartz_point3Pullback_eq G]
    exact (lowNormalSchwartz_point3Pullback G).smooth 1
  have hPart (a : A3) :
      MemLp (spatial3.d a (h3SchwartzPoint3Scalar G))
        (2 : ℝ≥0∞) (volume : Measure Point3) := by
    rw [h3SchwartzPoint3Scalar_spatial_d]
    let H : SchwartzMap V3 ℝ := ∂_{h3FourierAxisDirection a} G
    change MemLp (h3SchwartzPoint3Scalar H)
      (2 : ℝ≥0∞) (volume : Measure Point3)
    change MemLp ((H : V3 → ℝ) ∘
        (WithLp.toLp 2 : Point3 → V3))
      (2 : ℝ≥0∞) (volume : Measure Point3)
    exact (H.memLp (2 : ℝ≥0∞) (volume : Measure V3)).comp_measurePreserving
      (PiLp.volume_preserving_toLp A3)
  have hPartOfReal (a : A3) :
      MemLp (spatial3.d a (h3SchwartzPoint3Scalar G))
        (ENNReal.ofReal 2) (volume : Measure Point3) := by
    simpa only [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by norm_num] using hPart a
  have hD : MemLp (fun x : Point3 =>
      fderiv ℝ (h3SchwartzPoint3Scalar G) x)
      (2 : ℝ≥0∞) (volume : Measure Point3) := by
    simpa only [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by norm_num] using
      (hC1.fderiv_memLp_two_of_partials hPartOfReal)
  have hIntegral := lowNormalPoint3_fderiv_integral_sq_le_card_mul_partials
    (h3SchwartzPoint3Scalar G) hC1 hD hPart
  have hTransfer (a : A3) :
      (∫ x : Point3,
        ((spatial3.d a (h3SchwartzPoint3Scalar G)) x) ^ 2) =
      (∫ ξ : V3, ((∂_{h3FourierAxisDirection a} G) ξ) ^ 2) := by
    rw [h3SchwartzPoint3Scalar_spatial_d]
    exact h3Point3ToFourier_integral
      (fun ξ : V3 => ((∂_{h3FourierAxisDirection a} G) ξ) ^ 2)
  have hSumTransfer :
      (∑ a : A3, ∫ x : Point3,
        ((spatial3.d a (h3SchwartzPoint3Scalar G)) x) ^ 2) =
        (∑ a : A3, ∫ ξ : V3,
          ((∂_{h3FourierAxisDirection a} G) ξ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro a _
    exact hTransfer a
  rw [hSumTransfer] at hIntegral
  exact hIntegral


/-- Full third-order energy contributions control the integral of the
physical Fréchet-square of each ordered second Schwartz jet, including
all zero-energy cases and all three derivative directions. -/
theorem lowNormalRealSchwartz_secondJet_integratedFrechet_sq_le_thirdJetMass
    (f : A3 → SchwartzMap V3 ℝ) (j i k : A3) :
    (∫ x : Point3,
      ‖fderiv ℝ
        (h3SchwartzPoint3Scalar
          (∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection k} (f j)))) x‖ ^ 2) ≤
      (Fintype.card A3 : ℝ) *
        (∑ a : A3, ∫ ξ : V3,
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection i}
              (∂_{h3FourierAxisDirection k} (f j)))) ξ) ^ 2) := by
  exact lowNormalSchwartz_integral_physicalFrechet_sq_le_coordinateMass
    (∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k} (f j)))

end
end PrimeTensor.FirstMonomialTriad
