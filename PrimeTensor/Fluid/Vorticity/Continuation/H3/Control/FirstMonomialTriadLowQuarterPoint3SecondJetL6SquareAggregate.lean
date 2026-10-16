import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetFrechetFullEnergy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetHomogeneousSobolev

/-!
# Quantitative 27-jet squared L6 Sobolev aggregation

The existing homogeneous Sobolev inequality, applied to all 27 ordered
Schwartz second-derivative slots, gives an L6 bound for each jet in terms of
its actual physical Point3 Frechet derivative L2 norm.

This module squares that inequality in ENNReal and then sums it over all 27
slots without an additional cardinality loss. Both total masses are explicit
finite sums of *actual* eLpNorms. The factor from the physical sup-norm
carrier is not absorbed here; it is in the independent bound of the Frechet
square-integral total by the genuine 81-slot E3.

The forthcoming bridge must identify finite eLpNorm-two squares with the
corresponding real integral squares before combining these inequalities with
E3. This module does not assume that identity or a PDE/solenoidal property.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv ENNReal NNReal

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSecondJetL6SquareAggregate (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The fixed homogeneous Sobolev coefficient on the actual Point3 carrier. -/
noncomputable def lowNormalSecondJetSobolevConstant : ℝ≥0∞ :=
  ((MeasureTheory.SNormLESNormFDerivOfEqConst
    ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞)

/-- Squared L6 seminorm of one genuine second-order Schwartz jet. -/
noncomputable def lowNormalRealSchwartz_secondJetL6Square
    (f : A3 → SchwartzMap V3 ℝ) (j i k : A3) : ℝ≥0∞ :=
  (eLpNorm
      (∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j)) : SchwartzMap V3 ℝ)
      (ENNReal.ofReal 6) (volume : Measure V3)) ^ 2

/-- Squared physical Frechet-derivative L2 seminorm of that jet. -/
noncomputable def lowNormalRealSchwartz_secondJetFrechetL2Square
    (f : A3 → SchwartzMap V3 ℝ) (j i k : A3) : ℝ≥0∞ :=
  (eLpNorm (fun x : Point3 =>
      fderiv ℝ
        (h3SchwartzPoint3Scalar
          (∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection k} (f j)))) x)
      (ENNReal.ofReal 2) (volume : Measure Point3)) ^ 2

/-- Each of the 27 genuine Schwartz jets obeys the squared homogeneous
Sobolev bound, with the same fixed coefficient and no new assumptions. -/
theorem lowNormalRealSchwartz_secondJetL6Square_le_sobolev
    (f : A3 → SchwartzMap V3 ℝ) (j i k : A3) :
    lowNormalRealSchwartz_secondJetL6Square f j i k ≤
      lowNormalSecondJetSobolevConstant ^ 2 *
        lowNormalRealSchwartz_secondJetFrechetL2Square f j i k := by
  have h :=
    lowNormalRealSchwartz_secondJet_euclideanL6_le_physicalDerivativeL2
      f j i k
  change
    (eLpNorm
        (∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (f j)) : SchwartzMap V3 ℝ)
        (ENNReal.ofReal 6) (volume : Measure V3)) ^ 2 ≤
      lowNormalSecondJetSobolevConstant ^ 2 *
        (eLpNorm (fun x : Point3 =>
          fderiv ℝ
            (h3SchwartzPoint3Scalar
              (∂_{h3FourierAxisDirection i}
                (∂_{h3FourierAxisDirection k} (f j)))) x)
          (ENNReal.ofReal 2) (volume : Measure Point3)) ^ 2
  change
    eLpNorm
        (∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (f j)) : SchwartzMap V3 ℝ)
        (ENNReal.ofReal 6) (volume : Measure V3) ≤
      lowNormalSecondJetSobolevConstant *
        eLpNorm (fun x : Point3 =>
          fderiv ℝ
            (h3SchwartzPoint3Scalar
              (∂_{h3FourierAxisDirection i}
                (∂_{h3FourierAxisDirection k} (f j)))) x)
          (ENNReal.ofReal 2) (volume : Measure Point3) at h
  calc
    _ ≤ (lowNormalSecondJetSobolevConstant *
        eLpNorm (fun x : Point3 =>
          fderiv ℝ
            (h3SchwartzPoint3Scalar
              (∂_{h3FourierAxisDirection i}
                (∂_{h3FourierAxisDirection k} (f j)))) x)
          (ENNReal.ofReal 2) (volume : Measure Point3)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h 2
    _ = _ := mul_pow _ _ _

/-- The full 27-slot L6-square total; no selected channel is discarded. -/
noncomputable def lowNormalRealSchwartz_secondJetsL6SquareTotal
    (f : A3 → SchwartzMap V3 ℝ) : ℝ≥0∞ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3,
    lowNormalRealSchwartz_secondJetL6Square f j i k

/-- The corresponding 27-slot physical Frechet-derivative L2-square total. -/
noncomputable def lowNormalRealSchwartz_secondJetsFrechetL2SquareTotal
    (f : A3 → SchwartzMap V3 ℝ) : ℝ≥0∞ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3,
    lowNormalRealSchwartz_secondJetFrechetL2Square f j i k

/-- Aggregate any threefold finite family of pointwise majorants,
without a cardinality multiplier from the summation itself. -/
private theorem lowNormal_threefold_sum_le_const_mul
    {J : Type*} [Fintype J]
    (A B : J → J → J → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ j i k, A j i k ≤ C * B j i k) :
    (∑ j : J, ∑ i : J, ∑ k : J, A j i k) ≤
      C * (∑ j : J, ∑ i : J, ∑ k : J, B j i k) := by
  classical
  calc
    (∑ j : J, ∑ i : J, ∑ k : J, A j i k) ≤
        (∑ j : J, ∑ i : J, ∑ k : J, C * B j i k) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      exact h j i k
    _ = C * (∑ j : J, ∑ i : J, ∑ k : J, B j i k) := by
      simp only [← Finset.mul_sum]

/-- The complete homogeneous L6-square inequality over all 27 ordered
Schwartz jets, with exactly the same squared Sobolev constant as each slot.
The subsequent E3 bridge concerns only the L2-square-to-real-integral step. -/
theorem lowNormalRealSchwartz_secondJetsL6SquareTotal_le_sobolev
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_secondJetsL6SquareTotal f ≤
      lowNormalSecondJetSobolevConstant ^ 2 *
        lowNormalRealSchwartz_secondJetsFrechetL2SquareTotal f := by
  unfold lowNormalRealSchwartz_secondJetsL6SquareTotal
    lowNormalRealSchwartz_secondJetsFrechetL2SquareTotal
  exact lowNormal_threefold_sum_le_const_mul
    (lowNormalRealSchwartz_secondJetL6Square f)
    (lowNormalRealSchwartz_secondJetFrechetL2Square f)
    (lowNormalSecondJetSobolevConstant ^ 2)
    (lowNormalRealSchwartz_secondJetL6Square_le_sobolev f)

end
end PrimeTensor.FirstMonomialTriad
