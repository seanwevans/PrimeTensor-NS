import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetL6SquareAggregate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetFrechetFullEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Squared L² norms, physical real energies, and the 27-slot L⁶ bound

The quantitative homogeneous Sobolev aggregate is written in `ℝ≥0∞`.
The already proved full Fréchet energy estimate is an inequality of real
Bochner integrals. The bridge is the genuine L² identity

  (eLpNorm F 2 volume)² = ENNReal.ofReal (∫ x, ‖F x‖²),

under `MemLp F 2 volume`. We prove it for the actual physical derivative
space, apply it to all 27 Schwartz jets, and transport the finite real sums
using nonnegativity. Nothing is assumed about Navier–Stokes or solenoidality.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv ENNReal NNReal

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSecondJetL2NormIntegralBridge
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- For an actual square-integrable physical Fréchet field, the square of
its extended L² seminorm equals the real integral of its squared norm. -/
theorem lowNormalPoint3_memLp_two_eLpNorm_sq_eq_ofReal_integral
    (F : Point3 → (Point3 →L[ℝ] ℝ))
    (hF : MemLp F (ENNReal.ofReal 2) (volume : Measure Point3)) :
    (eLpNorm F (ENNReal.ofReal 2) (volume : Measure Point3)) ^ 2 =
      ENNReal.ofReal (∫ x : Point3, ‖F x‖ ^ 2) := by
  -- `eLpNorm_eq_integral_rpow_norm` returns a *real-exponent* square.
  -- Separate its conversion to the natural square: simp does not infer that
  -- exponent elaboration is interchangeable under the Bochner integral.
  have hFormulaReal :
      eLpNorm F (ENNReal.ofReal 2) (volume : Measure Point3) =
        ENNReal.ofReal
          ((∫ x : Point3, ‖F x‖ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)) := by
    simpa only [show (ENNReal.ofReal (2 : ℝ)).toReal = (2 : ℝ) by norm_num] using
      (hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp))
  have hIntegralPower :
      (∫ x : Point3, ‖F x‖ ^ (2 : ℝ)) =
        (∫ x : Point3, ‖F x‖ ^ (2 : ℕ)) := by
    apply integral_congr_ae
    filter_upwards with x
    exact Real.rpow_natCast (‖F x‖) 2
  have hFormula :
      eLpNorm F (ENNReal.ofReal 2) (volume : Measure Point3) =
        ENNReal.ofReal
          ((∫ x : Point3, ‖F x‖ ^ 2) ^ ((2 : ℝ)⁻¹)) := by
    rw [hIntegralPower] at hFormulaReal
    exact hFormulaReal
  have hNonneg : 0 ≤ (∫ x : Point3, ‖F x‖ ^ 2) :=
    integral_nonneg (fun x => sq_nonneg ‖F x‖)
  have hRoot :
      ((∫ x : Point3, ‖F x‖ ^ 2) ^ ((2 : ℝ)⁻¹)) ^ 2 =
        (∫ x : Point3, ‖F x‖ ^ 2) := by
    simpa [Real.sqrt_eq_rpow, one_div] using Real.sq_sqrt hNonneg
  calc
    (eLpNorm F (ENNReal.ofReal 2) (volume : Measure Point3)) ^ 2 =
        (ENNReal.ofReal
          ((∫ x : Point3, ‖F x‖ ^ 2) ^ ((2 : ℝ)⁻¹))) ^ 2 :=
      congrArg (fun y : ℝ≥0∞ => y ^ 2) hFormula
    _ = ENNReal.ofReal
          (((∫ x : Point3, ‖F x‖ ^ 2) ^ ((2 : ℝ)⁻¹)) ^ 2) :=
      (ENNReal.ofReal_pow (Real.rpow_nonneg hNonneg _) 2).symm
    _ = ENNReal.ofReal (∫ x : Point3, ‖F x‖ ^ 2) :=
      congrArg ENNReal.ofReal hRoot

/-- The actual physical Fréchet derivative of any pulled-back Schwartz
function lies in L²; no auxiliary derivative-integrability axiom. -/
theorem lowNormalSchwartz_physicalFrechet_memLp_two
    (g : SchwartzMap V3 ℝ) :
    MemLp (fun x : Point3 => fderiv ℝ (h3SchwartzPoint3Scalar g) x)
      (ENNReal.ofReal 2) (volume : Measure Point3) := by
  let G : SchwartzMap Point3 ℝ := lowNormalSchwartz_point3Pullback g
  have hC1 : SpatialC1 (G : Point3 → ℝ) := G.smooth 1
  have hDerivativeMeas : AEStronglyMeasurable
      (fun x : Point3 => fderiv ℝ (G : Point3 → ℝ) x)
      (volume : Measure Point3) :=
    (hC1.continuous_fderiv (by norm_num)).aestronglyMeasurable
  have hSchwartzNorm : MemLp (fun x : Point3 =>
      ‖(SchwartzMap.fderivCLM ℝ Point3 ℝ G) x‖)
      (ENNReal.ofReal 2) (volume : Measure Point3) :=
    ((SchwartzMap.fderivCLM ℝ Point3 ℝ G).memLp
      (ENNReal.ofReal 2) (volume : Measure Point3)).norm
  have hDerivativeNorm : MemLp (fun x : Point3 =>
      ‖fderiv ℝ (G : Point3 → ℝ) x‖)
      (ENNReal.ofReal 2) (volume : Measure Point3) := by
    simpa only [SchwartzMap.fderivCLM_apply] using hSchwartzNorm
  have hD : MemLp (fun x : Point3 => fderiv ℝ (G : Point3 → ℝ) x)
      (ENNReal.ofReal 2) (volume : Measure Point3) :=
    (memLp_norm_iff hDerivativeMeas).mp hDerivativeNorm
  simpa only [G, lowNormalSchwartz_point3Pullback_eq] using hD

/-- Each second jet's squared extended Fréchet L² norm equals its
actual real physical derivative-square integral. -/
theorem lowNormalRealSchwartz_secondJetFrechetL2Square_eq_ofReal_integral
    (f : A3 → SchwartzMap V3 ℝ) (j i k : A3) :
    lowNormalRealSchwartz_secondJetFrechetL2Square f j i k =
      ENNReal.ofReal (∫ x : Point3,
        ‖fderiv ℝ
          (h3SchwartzPoint3Scalar
            (∂_{h3FourierAxisDirection i}
              (∂_{h3FourierAxisDirection k} (f j)))) x‖ ^ 2) := by
  unfold lowNormalRealSchwartz_secondJetFrechetL2Square
  exact lowNormalPoint3_memLp_two_eLpNorm_sq_eq_ofReal_integral _
    (lowNormalSchwartz_physicalFrechet_memLp_two
      (∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j))))

/-- Abstract transfer of three nested nonnegative real sums into `ENNReal`.
All reindexing occurs on a generic finite type, avoiding large elaboration. -/
private theorem lowNormal_ofReal_threefold_sum
    {J : Type*} [Fintype J]
    (F : J → J → J → ℝ)
    (hF : ∀ j i k, 0 ≤ F j i k) :
    (∑ j : J, ∑ i : J, ∑ k : J, ENNReal.ofReal (F j i k)) =
      ENNReal.ofReal (∑ j : J, ∑ i : J, ∑ k : J, F j i k) := by
  classical
  let C : J → J → ℝ := fun j i => ∑ k : J, F j i k
  let B : J → ℝ := fun j => ∑ i : J, C j i
  have hK (j i : J) :
      (∑ k : J, ENNReal.ofReal (F j i k)) =
        ENNReal.ofReal (C j i) := by
    exact (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (f := F j i)
      (fun k _ => hF j i k)).symm
  have hI (j : J) :
      (∑ i : J, ENNReal.ofReal (C j i)) =
        ENNReal.ofReal (B j) := by
    exact (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (f := C j)
      (fun i _ => Finset.sum_nonneg (fun k _ => hF j i k))).symm
  have hJ :
      (∑ j : J, ENNReal.ofReal (B j)) =
        ENNReal.ofReal (∑ j : J, B j) := by
    exact (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (f := B)
      (fun j _ => Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun k _ => hF j i k)))).symm
  calc
    (∑ j : J, ∑ i : J, ∑ k : J, ENNReal.ofReal (F j i k)) =
        (∑ j : J, ∑ i : J, ENNReal.ofReal (C j i)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact hK j i
    _ = (∑ j : J, ENNReal.ofReal (B j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hI j
    _ = ENNReal.ofReal (∑ j : J, B j) := hJ
    _ = _ := rfl

/-- The full 27-slot extended Fréchet square mass equals the `ofReal`
image of the *existing*, integrated physical Fréchet energy. -/
theorem lowNormalRealSchwartz_secondJetsFrechetL2SquareTotal_eq_ofReal_energy
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_secondJetsFrechetL2SquareTotal f =
      ENNReal.ofReal (lowNormalRealSchwartzSecondJetPhysicalFrechetEnergy f) := by
  classical
  let M : A3 → A3 → A3 → ℝ := fun j i k =>
    ∫ x : Point3,
      ‖fderiv ℝ
        (h3SchwartzPoint3Scalar
          (∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection k} (f j)))) x‖ ^ 2
  have hM (j i k : A3) : 0 ≤ M j i k :=
    integral_nonneg (fun x => sq_nonneg _)
  have hOfRealSum := lowNormal_ofReal_threefold_sum M hM
  unfold lowNormalRealSchwartz_secondJetsFrechetL2SquareTotal
  calc
    (∑ j : A3, ∑ i : A3, ∑ k : A3,
      lowNormalRealSchwartz_secondJetFrechetL2Square f j i k) =
        (∑ j : A3, ∑ i : A3, ∑ k : A3, ENNReal.ofReal (M j i k)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact lowNormalRealSchwartz_secondJetFrechetL2Square_eq_ofReal_integral f j i k
    _ = ENNReal.ofReal (∑ j : A3, ∑ i : A3, ∑ k : A3, M j i k) := hOfRealSum
    _ = ENNReal.ofReal (lowNormalRealSchwartzSecondJetPhysicalFrechetEnergy f) := rfl

/-- The complete 27-slot homogeneous L⁶ bound now closes against the genuine
81-slot E3, with the physical sup-norm cardinality factor *still visible*. -/
theorem lowNormalRealSchwartz_secondJetsL6SquareTotal_le_sobolev_mul_E3
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_secondJetsL6SquareTotal f ≤
      lowNormalSecondJetSobolevConstant ^ 2 *
        ENNReal.ofReal
          ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f) := by
  calc
    lowNormalRealSchwartz_secondJetsL6SquareTotal f ≤
        lowNormalSecondJetSobolevConstant ^ 2 *
          lowNormalRealSchwartz_secondJetsFrechetL2SquareTotal f :=
      lowNormalRealSchwartz_secondJetsL6SquareTotal_le_sobolev f
    _ = lowNormalSecondJetSobolevConstant ^ 2 *
          ENNReal.ofReal
            (lowNormalRealSchwartzSecondJetPhysicalFrechetEnergy f) := by
      rw [lowNormalRealSchwartz_secondJetsFrechetL2SquareTotal_eq_ofReal_energy]
    _ ≤ lowNormalSecondJetSobolevConstant ^ 2 *
          ENNReal.ofReal
            ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f) := by
      exact mul_le_mul_of_nonneg_left
        (ENNReal.ofReal_le_ofReal
          (lowNormalRealSchwartz_secondJet_frechetEnergy_le_card_mul_E3 f))
        (by positivity)

end
end PrimeTensor.FirstMonomialTriad
