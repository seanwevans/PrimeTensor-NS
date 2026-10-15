import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualDilationPhysical
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SignReversal

/-!
# Exact isotropic dilation of the full physical 243-slot first monomial

The physical Point3 and H3 Fourier carriers already agree under the canonical
real Schwartz realization. The preceding checkpoints prove the spatial
chain rule, the actual dimension-three Jacobian, and all H3 energy sums.

The first monomial contains three differentiated factors of respective
orders 3, 2, and 2. Thus its seven spatial derivatives contribute
`scale ^ 7`, while the three-dimensional volume Jacobian contributes
`(scale ^ 3)⁻¹`. Their exact product is `scale ^ 4`.

The proof works on every real three-component Schwartz velocity; there are
no divergence, Fourier support, or Navier--Stokes path assumptions. It uses
the original five finite axis sums and the actual physical pairing, retaining
all 243 terms and their existing factor two.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterDilationMonomial (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceQuarterDilationMonomial :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The analytic 3+2+2 building block. Its factor is exactly the sum of
seven derivative degrees minus the three-dimensional Jacobian degree. -/
private theorem lowNormalSchwartz_three_two_two_integral_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (F G H : SchwartzMap V3 ℝ) :
    (∫ x : V3,
      (scale ^ 3 • lowNormalSchwartzDilation scale hscale F) x *
        ((scale ^ 2 • lowNormalSchwartzDilation scale hscale G) x *
          (scale ^ 2 • lowNormalSchwartzDilation scale hscale H) x)) =
      scale ^ 4 * ∫ x : V3, F x * (G x * H x) := by
  have hs : scale ≠ 0 := ne_of_gt hscale
  have hCoeff : scale ^ 7 * (scale ^ 3)⁻¹ = scale ^ 4 := by
    field_simp [hs]
  calc
    _ = ∫ x : V3, scale ^ 7 *
          (F (scale • x) * (G (scale • x) * H (scale • x))) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_apply, smul_eq_mul, lowNormalSchwartzDilation_apply]
      ring
    _ = scale ^ 7 * ∫ x : V3,
          F (scale • x) * (G (scale • x) * H (scale • x)) := by
      rw [integral_const_mul]
    _ = scale ^ 7 * ((scale ^ 3)⁻¹ *
          ∫ x : V3, F x * (G x * H x)) := by
      rw [lowNormalH3Fourier_integral_comp_positive_smul scale hscale
        (fun x : V3 => F x * (G x * H x))]
    _ = scale ^ 4 * ∫ x : V3, F x * (G x * H x) := by
      rw [← mul_assoc, hCoeff]

/-- One *actual Point3* first-monomial slot scales by the fourth power.
The physical factor two from `spatialEnergyPairing` remains in place. -/
theorem lowNormalRealSchwartzPoint3MonomialSlot_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) (j r i k l : A3) :
    spatialEnergyPairing
      (spatial3.d i (spatial3.d k (spatial3.d l
        (h3SchwartzPoint3Scalar
          (lowNormalSchwartzVelocityDilation scale hscale f j)))))
      (fun x =>
        spatial3.d k (spatial3.d l
          (h3SchwartzPoint3Scalar
            (lowNormalSchwartzVelocityDilation scale hscale f r))) x *
        spatial3.d i (spatial3.d r
          (h3SchwartzPoint3Scalar
            (lowNormalSchwartzVelocityDilation scale hscale f j))) x) =
      scale ^ 4 * spatialEnergyPairing
        (spatial3.d i (spatial3.d k (spatial3.d l
          (h3SchwartzPoint3Scalar (f j)))))
        (fun x =>
          spatial3.d k (spatial3.d l
            (h3SchwartzPoint3Scalar (f r))) x *
          spatial3.d i (spatial3.d r
            (h3SchwartzPoint3Scalar (f j))) x) := by
  simp only [h3SchwartzPoint3_firstMonomial_pairing]
  -- Expose the componentwise Schwartz dilation before rewriting derivatives.
  simp only [lowNormalSchwartzVelocityDilation]
  rw [lowNormalSchwartzDilation_threeLineDerivs scale hscale
    (h3FourierAxisDirection i) (h3FourierAxisDirection k)
    (h3FourierAxisDirection l) (f j)]
  rw [lowNormalSchwartzDilation_twoLineDerivs scale hscale
    (h3FourierAxisDirection k) (h3FourierAxisDirection l) (f r)]
  rw [lowNormalSchwartzDilation_twoLineDerivs scale hscale
    (h3FourierAxisDirection i) (h3FourierAxisDirection r) (f j)]
  rw [lowNormalSchwartz_three_two_two_integral_dilation]
  ring

/-- The complete physical 243-slot cubic first-monomial integral is
homogeneous of degree FOUR under positive isotropic spatial dilation.
No component, direction, signed term, or physical normalization is dropped. -/
theorem lowNormalRealSchwartzPoint3Monomial_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzPoint3Monomial
        (lowNormalSchwartzVelocityDilation scale hscale f) =
      scale ^ 4 * lowNormalRealSchwartzPoint3Monomial f := by
  unfold lowNormalRealSchwartzPoint3Monomial
  simp_rw [lowNormalRealSchwartzPoint3MonomialSlot_dilation scale hscale f]
  simp only [← Finset.mul_sum]

end
end PrimeTensor.FirstMonomialTriad
