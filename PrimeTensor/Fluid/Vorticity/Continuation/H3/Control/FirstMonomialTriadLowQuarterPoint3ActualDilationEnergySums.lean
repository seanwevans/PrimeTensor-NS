import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualDilationJacobian
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3AmplitudeScaling

/-!
# Actual three-dimensional Schwartz H3 energy sums under spatial dilation

The preceding Jacobian module proves the exact change-of-variables formulas
for each real Schwartz directional derivative through fourth order. This
module sums those *proved integral identities* over every physical velocity
component and every ordered spatial derivative direction.

There are respectively 3, 9, 27 and 81 scalar integrals at derivative
orders zero, one, two and three. The preexisting top-dissipation definition
includes all 243 ordered fourth-derivative integrals. No selected channel,
positivity hypothesis, or scalar surrogate is used to obtain the equalities.

The unnormalized coefficients are (scale^3)^(-1), scale^2*(scale^3)^(-1),
scale^4*(scale^3)^(-1), scale^6*(scale^3)^(-1), and
scale^8*(scale^3)^(-1). For positive scale these have spatial degrees
-3, -1, +1, +3, and +5 respectively.

The normalization constant of the genuine H3 energy remains exactly one.
This result does not yet identify a physical Point3 dilation, transfer the
solenoidal constraint, or prove scale^4 homogeneity of the signed 243-slot
first monomial. Those are distinct subsequent analytic obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterEnergyDilation (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Full zeroth-order square mass, summed over all three velocity components. -/
noncomputable def lowNormalRealSchwartzH3Energy0
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∫ x : V3, (f j x) ^ 2

/-- Full first-order mass, with all nine ordered component/direction slots. -/
noncomputable def lowNormalRealSchwartzH3Energy1
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∫ x : V3,
    ((∂_{h3FourierAxisDirection i} (f j)) x) ^ 2

/-- Full second-order mass, with all 27 ordered slots. -/
noncomputable def lowNormalRealSchwartzH3Energy2
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∫ x : V3,
    ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k} (f j))) x) ^ 2

/-- Full third-order mass, with all 81 ordered slots. -/
noncomputable def lowNormalRealSchwartzH3Energy3
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∫ x : V3,
    ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k}
        (∂_{h3FourierAxisDirection l} (f j)))) x) ^ 2

/-- The normalized, full componentwise real Schwartz H3 energy. -/
noncomputable def lowNormalRealSchwartzH3Energy
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  1 + lowNormalRealSchwartzH3Energy0 f
    + lowNormalRealSchwartzH3Energy1 f
    + lowNormalRealSchwartzH3Energy2 f
    + lowNormalRealSchwartzH3Energy3 f

/-- Zeroth-order energy receives precisely the actual inverse volume factor. -/
theorem lowNormalRealSchwartzH3Energy0_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy0
      (lowNormalSchwartzVelocityDilation scale hscale f) =
      (scale ^ 3)⁻¹ * lowNormalRealSchwartzH3Energy0 f := by
  unfold lowNormalRealSchwartzH3Energy0 lowNormalSchwartzVelocityDilation
  simp_rw [lowNormalSchwartzDilation_integral_sq]
  simp only [← Finset.mul_sum]

/-- All nine first-order terms receive one common squared-gradient factor. -/
theorem lowNormalRealSchwartzH3Energy1_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy1
      (lowNormalSchwartzVelocityDilation scale hscale f) =
      (scale ^ 2 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy1 f := by
  unfold lowNormalRealSchwartzH3Energy1 lowNormalSchwartzVelocityDilation
  simp_rw [lowNormalSchwartzDilation_integral_sq_lineDeriv]
  simp only [← Finset.mul_sum]

/-- All 27 second-order terms receive the precise fourth-power factor. -/
theorem lowNormalRealSchwartzH3Energy2_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy2
      (lowNormalSchwartzVelocityDilation scale hscale f) =
      (scale ^ 4 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy2 f := by
  unfold lowNormalRealSchwartzH3Energy2 lowNormalSchwartzVelocityDilation
  simp_rw [lowNormalSchwartzDilation_integral_sq_twoLineDerivs]
  simp only [← Finset.mul_sum]

/-- All 81 third-order terms receive the precise sixth-power factor. -/
theorem lowNormalRealSchwartzH3Energy3_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy3
      (lowNormalSchwartzVelocityDilation scale hscale f) =
      (scale ^ 6 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy3 f := by
  unfold lowNormalRealSchwartzH3Energy3 lowNormalSchwartzVelocityDilation
  simp_rw [lowNormalSchwartzDilation_integral_sq_threeLineDerivs]
  simp only [← Finset.mul_sum]

/-- Every one of the existing 243 fourth-order dissipation slots scales
with the same eighth-power derivative factor and inverse-volume Jacobian. -/
theorem lowNormalRealSchwartzH3TopDissipation_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3TopDissipation
      (lowNormalSchwartzVelocityDilation scale hscale f) =
      (scale ^ 8 * (scale ^ 3)⁻¹) *
        lowNormalRealSchwartzH3TopDissipation f := by
  unfold lowNormalRealSchwartzH3TopDissipation lowNormalSchwartzVelocityDilation
  simp_rw [lowNormalSchwartzDilation_integral_sq_fourLineDerivs]
  simp only [← Finset.mul_sum]

/-- Exact four-order physical scaling of the *normalized* H3 energy.
In particular the constant `1` does not acquire a Jacobian factor. -/
theorem lowNormalRealSchwartzH3Energy_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy
      (lowNormalSchwartzVelocityDilation scale hscale f) =
      1 + (scale ^ 3)⁻¹ * lowNormalRealSchwartzH3Energy0 f
        + (scale ^ 2 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy1 f
        + (scale ^ 4 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy2 f
        + (scale ^ 6 * (scale ^ 3)⁻¹) * lowNormalRealSchwartzH3Energy3 f := by
  simp only [lowNormalRealSchwartzH3Energy,
    lowNormalRealSchwartzH3Energy0_dilation,
    lowNormalRealSchwartzH3Energy1_dilation,
    lowNormalRealSchwartzH3Energy2_dilation,
    lowNormalRealSchwartzH3Energy3_dilation]

end
end PrimeTensor.FirstMonomialTriad
