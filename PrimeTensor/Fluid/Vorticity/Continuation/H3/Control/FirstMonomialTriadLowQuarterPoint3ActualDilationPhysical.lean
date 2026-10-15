import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualDilationEnergySums
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPhysicalTransport

/-!
# Actual physical Point3 dilation and incompressibility

The existing real Schwartz dilation operates on the intrinsic Euclidean H3
carrier. This module proves that the canonical physical Point3 realization
commutes with that spatial dilation, and transports the first directional
chain rule to the project's actual `spatial3.d` operator.

In particular, physical divergence transforms as the first spatial
derivative: div(f(scale * ·)) = scale * (div f)(scale * ·). Therefore any
real Schwartz velocity with vanishing actual Point3 divergence remains
solenoidal under every strictly positive isotropic dilation.

No equality for the signed cubic 243-slot first monomial is asserted here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterPhysicalDilation (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical physical Point3-to-H3 linear map respects isotropic scale. -/
theorem lowNormalH3Point3ToFourier_smul
    (scale : ℝ) (x : Point3) :
    h3Point3ToFourierCLM (scale • x) =
      scale • h3Point3ToFourierCLM x := by
  exact map_smul h3Point3ToFourierCLM scale x

/-- Realize all three real Schwartz velocity components on actual `Point3`. -/
noncomputable def lowNormalRealSchwartzPoint3Velocity
    (f : A3 → SchwartzMap V3 ℝ) : A3 → ScalarField3 :=
  fun j => h3SchwartzPoint3Scalar (f j)

/-- The velocity constructed by *Schwartz* dilation equals the literal
physical Point3 dilation, with no coordinate permutation or scalar factor. -/
theorem lowNormalRealSchwartzPoint3Velocity_dilation_apply
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) (j : A3) (x : Point3) :
    lowNormalRealSchwartzPoint3Velocity
        (lowNormalSchwartzVelocityDilation scale hscale f) j x =
      lowNormalRealSchwartzPoint3Velocity f j (scale • x) := by
  change (lowNormalSchwartzDilation scale hscale (f j))
      (h3Point3ToFourierCLM x) =
    f j (h3Point3ToFourierCLM (scale • x))
  rw [lowNormalSchwartzDilation_apply,
    lowNormalH3Point3ToFourier_smul]

/-- The project's genuine physical coordinate derivative has the exact
first-order dilation chain rule. -/
theorem lowNormalRealSchwartzPoint3Velocity_spatial_d_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) (j i : A3) (x : Point3) :
    spatial3.d i
        (lowNormalRealSchwartzPoint3Velocity
          (lowNormalSchwartzVelocityDilation scale hscale f) j) x =
      scale * spatial3.d i (lowNormalRealSchwartzPoint3Velocity f j)
        (scale • x) := by
  change spatial3.d i
      (h3SchwartzPoint3Scalar (lowNormalSchwartzDilation scale hscale (f j))) x =
    scale * spatial3.d i (h3SchwartzPoint3Scalar (f j)) (scale • x)
  simp only [h3SchwartzPoint3Scalar_spatial_d,
    lowNormalSchwartzDilation_lineDeriv]
  change (scale • lowNormalSchwartzDilation scale hscale
      (∂_{h3FourierAxisDirection i} (f j))) (h3Point3ToFourierCLM x) =
    scale * ((∂_{h3FourierAxisDirection i} (f j))
      (h3Point3ToFourierCLM (scale • x)))
  simp only [smul_apply, smul_eq_mul, lowNormalSchwartzDilation_apply,
    lowNormalH3Point3ToFourier_smul]

/-- The full three-coordinate physical divergence, without dropping a
component, transforms by precisely one factor of the dilation. -/
theorem lowNormalRealSchwartzPoint3Velocity_divergence_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) (x : Point3) :
    (∑ j : A3, spatial3.d j
        (lowNormalRealSchwartzPoint3Velocity
          (lowNormalSchwartzVelocityDilation scale hscale f) j) x) =
      scale * (∑ j : A3,
        spatial3.d j (lowNormalRealSchwartzPoint3Velocity f j)
          (scale • x)) := by
  classical
  simp_rw [lowNormalRealSchwartzPoint3Velocity_spatial_d_dilation]
  rw [Finset.mul_sum]

/-- A divergence-free *physical Point3* Schwartz field stays divergence
free after genuine positive spatial dilation. No Fourier constraint is
introduced as an additional assumption. -/
theorem lowNormalRealSchwartzPoint3Velocity_divergence_zero_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : ∀ x : Point3,
      ∑ j : A3, spatial3.d j (lowNormalRealSchwartzPoint3Velocity f j) x = 0) :
    ∀ x : Point3,
      ∑ j : A3, spatial3.d j
        (lowNormalRealSchwartzPoint3Velocity
          (lowNormalSchwartzVelocityDilation scale hscale f) j) x = 0 := by
  intro x
  rw [lowNormalRealSchwartzPoint3Velocity_divergence_dilation]
  rw [hDiv (scale • x), mul_zero]

end
end PrimeTensor.FirstMonomialTriad
