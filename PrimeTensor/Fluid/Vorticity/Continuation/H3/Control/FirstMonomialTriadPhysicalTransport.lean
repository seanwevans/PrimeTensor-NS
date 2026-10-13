import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadDivergence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialAggregate
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Point3.Frechet.Continuity

/-!
# Real Schwartz transport to the project's physical first monomial

Pullback along the canonical Point3-to-Euclidean map commutes with the
actual spatial derivative and preserves the volume integral. Consequently
all three derivative factors in the physical first monomial are exactly
the corresponding Schwartz directional derivatives, without assumptions
about those derivatives beyond a Schwartz realization of the components.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3TriadPhysical (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TriadPhysical : MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

/-- A real Schwartz scalar viewed as an actual Point3 scalar field. -/
def h3SchwartzPoint3Scalar (f : SchwartzMap V3 ℝ) : ScalarField3 :=
  fun x => f (h3Point3ToFourierCLM x)

/-- Pullback commutes with one genuine coordinate derivative, hence can be
iterated for every derivative factor in the first monomial. -/
theorem h3SchwartzPoint3Scalar_spatial_d (f : SchwartzMap V3 ℝ) (i : A3) :
    spatial3.d i (h3SchwartzPoint3Scalar f) =
      h3SchwartzPoint3Scalar (∂_{h3FourierAxisDirection i} f) := by
  classical
  funext x
  have hline_eq (t : ℝ) :
      h3Point3ToFourierCLM (coordinateLine x i t) =
        h3Point3ToFourierCLM x + (t - x i) • h3FourierAxisDirection i := by
    ext j
    change coordinateLine x i t j = x j + (t - x i) * axisDirection i j
    by_cases hji : j = i
    · subst j
      simp only [coordinateLine_same, axisDirection_same, mul_one]
      ring
    · rw [coordinateLine_other x hji t, axisDirection_other hji]
      ring
  have hline :=
    (((hasDerivAt_id (x i)).sub_const (x i)).smul_const
      (h3FourierAxisDirection i)).const_add (h3Point3ToFourierCLM x)
  simp only [one_smul, id_eq] at hline
  have hd := (f.hasFDerivAt (h3Point3ToFourierCLM x)).comp_hasDerivAt_of_eq
    (x i) hline (by simp)
  change partialDeriv i (h3SchwartzPoint3Scalar f) x = _
  apply partialDeriv_eq_of_hasDerivAt
  simpa only [h3SchwartzPoint3Scalar, hline_eq, Function.comp_def,
    SchwartzMap.lineDerivOp_apply_eq_fderiv] using hd

/-- The two carriers have exactly the same volume integral under this map. -/
theorem h3Point3ToFourier_integral (f : V3 → ℝ) :
    (∫ x : Point3, f (h3Point3ToFourierCLM x)) = ∫ x : V3, f x := by
  have he : MeasurableEmbedding (WithLp.toLp 2 : Point3 → V3) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : A3 => ℝ)).symm.toHomeomorph.measurableEmbedding
  change (∫ x : Point3, f ((WithLp.toLp 2 : Point3 → V3) x)) = _
  exact (PiLp.volume_preserving_toLp A3).integral_comp he f

/-- Physical energy pairing of two real Schwartz pullbacks. -/
theorem spatialEnergyPairing_h3SchwartzPoint3Scalar (f g : SchwartzMap V3 ℝ) :
    spatialEnergyPairing (h3SchwartzPoint3Scalar f) (h3SchwartzPoint3Scalar g) =
      2 * ∫ x : V3, f x * g x := by
  unfold spatialEnergyPairing h3SchwartzPoint3Scalar
  rw [h3Point3ToFourier_integral (fun x => f x * g x)]

/-- Physical first-monomial pairing of three real Schwartz pullbacks. -/
theorem h3SchwartzPoint3_firstMonomial_pairing
    (f g h : SchwartzMap V3 ℝ) (i k l v : A3) :
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k (spatial3.d l (h3SchwartzPoint3Scalar f))))
      (fun x => spatial3.d k (spatial3.d l (h3SchwartzPoint3Scalar g)) x *
        spatial3.d i (spatial3.d v (h3SchwartzPoint3Scalar h)) x) =
    2 * ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} f))) x) *
      (((∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} g)) x) *
        ((∂_{h3FourierAxisDirection i} (∂_{h3FourierAxisDirection v} h)) x)) := by
  simp only [h3SchwartzPoint3Scalar_spatial_d]
  unfold spatialEnergyPairing h3SchwartzPoint3Scalar
  exact congrArg (fun r : ℝ => 2 * r) (h3Point3ToFourier_integral (fun x =>
    ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} f))) x) *
    (((∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} g)) x) *
      ((∂_{h3FourierAxisDirection i} (∂_{h3FourierAxisDirection v} h)) x))))

/-- Identify an existing path monomial from a Schwartz realization of its
logged velocity components. No derivative matching assumptions are needed. -/
theorem h3PathCanonicalFirstMonomial_eq_realSchwartz
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (j i k l v : A3) :
    h3PathCanonicalInterpolationMonomialPairing u t j i k l v 0 =
      2 * ∫ x : V3,
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} (f j)))) x) *
        (((∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} (f v))) x) *
          ((∂_{h3FourierAxisDirection i} (∂_{h3FourierAxisDirection v} (f j))) x)) := by
  simp only [h3PathCanonicalInterpolationMonomialPairing, ite_true]
  unfold thirdOrderInterpolationMonomial1
  rw [hRealization j, hRealization v]
  exact h3SchwartzPoint3_firstMonomial_pairing (f j) (f v) (f j) i k l v

/-- The entire existing physical aggregate is the sum of the transported
real Schwartz monomials, retaining the original physical index order. -/
theorem h3PathCanonicalFirstMonomialAggregate_eq_realSchwartz
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    h3PathCanonicalFirstMonomialAggregateAt u t =
      2 * (∑ j, ∑ v, ∑ i, ∑ k, ∑ l, ∫ x : V3,
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} (f j)))) x) *
        (((∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} (f v))) x) *
          ((∂_{h3FourierAxisDirection i} (∂_{h3FourierAxisDirection v} (f j))) x))) := by
  classical
  unfold h3PathCanonicalFirstMonomialAggregateAt
  simp only [h3PathCanonicalFirstMonomial_eq_realSchwartz u t f hRealization, Finset.mul_sum]

end
end PrimeTensor.Bridge.Euclidean
