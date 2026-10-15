import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3CriticalHalfUniformShape

/-!
# A two-parameter homogeneous shape invariant for the actual H3 first monomial

The preceding theorem characterizes the endpoint estimate by an unnormalized
homogeneous threshold on real Schwartz velocities. Here we use *both* actual
scaling actions: multiplying all velocity components by a real amplitude and
pulling them back by a positive isotropic spatial dilation.

For the complete physical monomial `M`, fourth-order dissipation `D`,
zeroth-order energy `E0`, and third-order energy `E3`, the polynomial

  M^12 - C^12 * D^12 * E0^5 * E3

has degree 36 in velocity amplitude and degree 48 in spatial dilation.
The weights `5` and `1` are forced by matching the seven-derivative cubic
monomial to the fourth-order dissipation and the two extreme H3 masses.

This is an invariant *test quantity*, not an established universal bound:
positive excess is not asserted to exist, and the contribution of E1 and E2
to the full H3 energy has not been estimated away.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeBalancedShape (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- No division is taken: the test is meaningful even for zero mass or
zero top dissipation. Its two summands have matching scaling degrees. -/
noncomputable def lowNormalRealSchwartz_criticalHalfBalancedExcess
    (C : ℝ) (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  (lowNormalRealSchwartzPoint3Monomial f) ^ 12 -
    C ^ 12 * (lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
      (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
      lowNormalRealSchwartzH3Energy3 f

/-- The zero-derivative quadratic mass has exact amplitude degree two. -/
theorem lowNormalRealSchwartzH3Energy0_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy0 (fun j => a • f j) =
      a ^ 2 * lowNormalRealSchwartzH3Energy0 f := by
  change lowNormalRealSchwartzH3Square0 (fun j => a • f j) =
    a ^ 2 * lowNormalRealSchwartzH3Square0 f
  exact lowNormalRealSchwartzH3Square0_real_smul a f

/-- The third-derivative quadratic mass also has amplitude degree two. -/
theorem lowNormalRealSchwartzH3Energy3_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy3 (fun j => a • f j) =
      a ^ 2 * lowNormalRealSchwartzH3Energy3 f := by
  change lowNormalRealSchwartzH3Square3 (fun j => a • f j) =
    a ^ 2 * lowNormalRealSchwartzH3Square3 f
  exact lowNormalRealSchwartzH3Square3_real_smul a f

/-- Both sides of the balanced test have total amplitude degree 36. -/
theorem lowNormalRealSchwartz_criticalHalfBalancedExcess_real_smul
    (C a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_criticalHalfBalancedExcess C
        (fun j : A3 => a • f j) =
      a ^ 36 * lowNormalRealSchwartz_criticalHalfBalancedExcess C f := by
  unfold lowNormalRealSchwartz_criticalHalfBalancedExcess
  rw [lowNormalRealSchwartzPoint3Monomial_real_smul,
    lowNormalRealSchwartzH3TopDissipation_real_smul,
    lowNormalRealSchwartzH3Energy0_real_smul,
    lowNormalRealSchwartzH3Energy3_real_smul]
  ring

/-- The spatial coefficient carried by D^12 * E0^5 * E3 is exactly
`scale^48`, matching the twelfth power of the degree-four monomial. -/
private theorem lowNormal_balanced_spatial_coefficient
    (scale : ℝ) (hscale : 0 < scale) :
    ((scale ^ 8 * (scale ^ 3)⁻¹) ^ 12 *
      ((scale ^ 3)⁻¹) ^ 5) *
      (scale ^ 6 * (scale ^ 3)⁻¹) = scale ^ 48 := by
  have hs : scale ≠ 0 := ne_of_gt hscale
  field_simp [hs]

/-- Under actual Euclidean/Point3 dilation, each term of the balanced
shape polynomial has spatial degree 48. -/
theorem lowNormalRealSchwartz_criticalHalfBalancedExcess_dilation
    (C scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_criticalHalfBalancedExcess C
        (lowNormalSchwartzVelocityDilation scale hscale f) =
      scale ^ 48 * lowNormalRealSchwartz_criticalHalfBalancedExcess C f := by
  unfold lowNormalRealSchwartz_criticalHalfBalancedExcess
  rw [lowNormalRealSchwartzPoint3Monomial_dilation,
    lowNormalRealSchwartzH3TopDissipation_dilation,
    lowNormalRealSchwartzH3Energy0_dilation,
    lowNormalRealSchwartzH3Energy3_dilation]
  have hCoeff := lowNormal_balanced_spatial_coefficient scale hscale
  -- Name the four physical quantities to keep the polynomial calculation small.
  let M : ℝ := lowNormalRealSchwartzPoint3Monomial f
  let D : ℝ := lowNormalRealSchwartzH3TopDissipation f
  let E0 : ℝ := lowNormalRealSchwartzH3Energy0 f
  let E3 : ℝ := lowNormalRealSchwartzH3Energy3 f
  change (scale ^ 4 * M) ^ 12 -
      C ^ 12 * ((scale ^ 8 * (scale ^ 3)⁻¹) * D) ^ 12 *
        ((scale ^ 3)⁻¹ * E0) ^ 5 *
        ((scale ^ 6 * (scale ^ 3)⁻¹) * E3) =
    scale ^ 48 * (M ^ 12 - C ^ 12 * D ^ 12 * E0 ^ 5 * E3)
  have hPow : (scale ^ 4) ^ 12 = scale ^ 48 := by ring
  -- A genuine three-step calculation: expand products, apply the already
  -- proved Jacobian coefficient identity, and factor out scale^48.
  calc
    _ = (scale ^ 4) ^ 12 * M ^ 12 -
          C ^ 12 *
            (((scale ^ 8 * (scale ^ 3)⁻¹) ^ 12 *
                ((scale ^ 3)⁻¹) ^ 5) *
              (scale ^ 6 * (scale ^ 3)⁻¹)) *
            (D ^ 12 * E0 ^ 5 * E3) := by ring
    _ = scale ^ 48 * M ^ 12 -
          C ^ 12 * scale ^ 48 * (D ^ 12 * E0 ^ 5 * E3) := by
      rw [hPow, hCoeff]
    _ = scale ^ 48 * (M ^ 12 - C ^ 12 * D ^ 12 * E0 ^ 5 * E3) := by
      ring

/-- The original physical incompressibility constraint is also closed under
positive isotropic Schwartz spatial dilation. -/
theorem lowNormalRealSchwartz_Point3Solenoidal_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f) :
    lowNormalRealSchwartz_Point3Solenoidal
      (lowNormalSchwartzVelocityDilation scale hscale f) := by
  change ∀ x : Point3,
    ∑ j : A3, spatial3.d j
      (lowNormalRealSchwartzPoint3Velocity
        (lowNormalSchwartzVelocityDilation scale hscale f) j) x = 0
  exact lowNormalRealSchwartzPoint3Velocity_divergence_zero_dilation
    scale hscale f hDiv

/-- A strictly positive balanced excess stays positive under every
positive amplitude rescaling of all three velocity components. -/
theorem lowNormalRealSchwartz_positiveBalancedExcess_real_smul
    (C a : ℝ) (ha : 0 < a)
    (f : A3 → SchwartzMap V3 ℝ)
    (hExcess : 0 < lowNormalRealSchwartz_criticalHalfBalancedExcess C f) :
    0 < lowNormalRealSchwartz_criticalHalfBalancedExcess C
      (fun j : A3 => a • f j) := by
  rw [lowNormalRealSchwartz_criticalHalfBalancedExcess_real_smul]
  exact mul_pos (pow_pos ha 36) hExcess

/-- The same strict excess remains positive under every positive physical
spatial dilation; the assertion concerns an actual real Schwartz velocity. -/
theorem lowNormalRealSchwartz_positiveBalancedExcess_dilation
    (C scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ)
    (hExcess : 0 < lowNormalRealSchwartz_criticalHalfBalancedExcess C f) :
    0 < lowNormalRealSchwartz_criticalHalfBalancedExcess C
      (lowNormalSchwartzVelocityDilation scale hscale f) := by
  rw [lowNormalRealSchwartz_criticalHalfBalancedExcess_dilation]
  exact mul_pos (pow_pos hscale 48) hExcess

end
end PrimeTensor.FirstMonomialTriad
