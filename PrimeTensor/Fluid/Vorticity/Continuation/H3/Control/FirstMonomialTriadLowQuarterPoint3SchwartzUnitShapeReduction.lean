import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzShapeOrbitNormalization

/-!
# Exact reduction of the solenoidal critical-half shape ratio to unit endpoints

For every real Schwartz velocity with positive zeroth- and third-order energy,
existing dilation and amplitude identities produce a representative with
`E0 = E3 = 1`, preserving the signed monomial's dimensionless ratio.

We prove that a bound for this ratio on ALL positive-endpoint solenoidal
profiles is equivalent to precisely the same bound on the unit-endpoint
solenoidal class. The coefficient is unchanged. On that class the genuine
intermediate energies satisfy `E1 <= 1`, `E2 <= 1`, and the complete
quadratic energy is at most 4, using the already proved sharp Cauchy bounds.

For positive fourth-order dissipation, the normalized shape-ratio inequality
is exactly the elementary signed monomial twelfth-power inequality; no
unknown scale remains. A proposed uniform critical-half coefficient implies
its necessary ratio bound on the normalized class, including the case of
zero fourth-order dissipation. No converse or witness is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeUnitShapeReduction (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- A real number whose cube is at most one is at most one; a division-free
comparison that also covers negative values. -/
private theorem criticalHalf_cube_le_one (x : ℝ)
    (hx : x ^ 3 ≤ 1) : x ≤ 1 := by
  by_contra hn
  have hlt : (1 : ℝ) < x := lt_of_not_ge hn
  have hp : (1 : ℝ) ^ 3 < x ^ 3 :=
    pow_lt_pow_left₀ hlt (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
  have hpOne : (1 : ℝ) < x ^ 3 := by
    simpa only [one_pow] using hp
  exact (not_lt_of_ge hx) hpOne

/-- On the actual unit-endpoint Schwartz class, both intermediate energy
blocks are at most one, with their exact coefficient-one constant. -/
theorem lowNormalRealSchwartz_unitEndpoints_intermediate_le_one
    (f : A3 → SchwartzMap V3 ℝ)
    (h0 : lowNormalRealSchwartzH3Energy0 f = 1)
    (h3 : lowNormalRealSchwartzH3Energy3 f = 1) :
    lowNormalRealSchwartzH3Energy1 f ≤ 1 ∧
      lowNormalRealSchwartzH3Energy2 f ≤ 1 := by
  obtain ⟨hOne, hTwo⟩ := lowNormalRealSchwartzH3Energy_sharp_cubicLogConvex f
  have hOneUnit : (lowNormalRealSchwartzH3Energy1 f) ^ 3 ≤ 1 := by
    simpa [h0, h3] using hOne
  have hTwoUnit : (lowNormalRealSchwartzH3Energy2 f) ^ 3 ≤ 1 := by
    simpa [h0, h3] using hTwo
  exact ⟨criticalHalf_cube_le_one _ hOneUnit,
    criticalHalf_cube_le_one _ hTwoUnit⟩

/-- The complete UNNORMALIZED quadratic H3 energy on this unit-endpoint
class is at most four, still accounting for all 120 zeroth-through-third
ordered derivative slots. -/
theorem lowNormalRealSchwartz_unitEndpoints_quadratic_le_four
    (f : A3 → SchwartzMap V3 ℝ)
    (h0 : lowNormalRealSchwartzH3Energy0 f = 1)
    (h3 : lowNormalRealSchwartzH3Energy3 f = 1) :
    lowNormalRealSchwartzH3EnergyQuadratic f ≤ 4 := by
  have hBalance : (1 : ℝ) ^ 6 * lowNormalRealSchwartzH3Energy3 f =
      lowNormalRealSchwartzH3Energy0 f := by
    rw [h0, h3]
    norm_num
  have hBound := lowNormalRealSchwartzH3Energy_sharp_balancedScale_upper
    f 1 (by norm_num) (by rw [h0]; norm_num) hBalance
  rw [lowNormalRealSchwartzH3EnergyQuadratic_eq_sum]
  simpa [h0, h3] using hBound

/-- EXACT equivalence, at the SAME proposed constant K, of global
positive-endpoint ratio control and control on solenoidal unit-endpoint
Schwartz representatives. No top-dissipation positivity is required. -/
theorem lowNormalRealSchwartz_positiveEndpoints_ratioBound_iff_unitEndpoints
    (K : ℝ) :
    (∀ f : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal f →
      0 < lowNormalRealSchwartzH3Energy0 f →
      0 < lowNormalRealSchwartzH3Energy3 f →
      lowNormalRealSchwartz_sharpShapeRatio f ≤ K) ↔
    (∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      lowNormalRealSchwartzH3Energy0 g = 1 →
      lowNormalRealSchwartzH3Energy3 g = 1 →
      lowNormalRealSchwartz_sharpShapeRatio g ≤ K) := by
  constructor
  · intro hAll g hDiv h0 h3
    exact hAll g hDiv (by rw [h0]; norm_num) (by rw [h3]; norm_num)
  · intro hUnit f hDiv hE0 hE3
    obtain ⟨scale, hscale, a, ha, h0g, h3g, hRatio⟩ :=
      lowNormalRealSchwartz_positiveEndpoints_exist_unitOrbitRepresentative
        f hE0 hE3
    let g : A3 → SchwartzMap V3 ℝ :=
      fun j => a • (lowNormalSchwartzVelocityDilation scale hscale f j)
    have hDivScale : lowNormalRealSchwartz_Point3Solenoidal
        (lowNormalSchwartzVelocityDilation scale hscale f) :=
      lowNormalRealSchwartz_Point3Solenoidal_dilation scale hscale f hDiv
    have hDivg : lowNormalRealSchwartz_Point3Solenoidal g :=
      lowNormalRealSchwartz_Point3Solenoidal_real_smul a
        (lowNormalSchwartzVelocityDilation scale hscale f) hDivScale
    have hBound : lowNormalRealSchwartz_sharpShapeRatio g ≤ K :=
      hUnit g hDivg h0g h3g
    calc
      lowNormalRealSchwartz_sharpShapeRatio f =
          lowNormalRealSchwartz_sharpShapeRatio g := hRatio.symm
      _ ≤ K := hBound

/-- At strictly positive D and unit endpoint energies, a ratio bound is
EXACTLY the twelfth-power signed-monomial bound against D alone. -/
theorem lowNormalRealSchwartz_unitEndpoints_ratio_le_iff_monomial
    (K : ℝ) (f : A3 → SchwartzMap V3 ℝ)
    (h0 : lowNormalRealSchwartzH3Energy0 f = 1)
    (h3 : lowNormalRealSchwartzH3Energy3 f = 1)
    (hD : 0 < lowNormalRealSchwartzH3TopDissipation f) :
    lowNormalRealSchwartz_sharpShapeRatio f ≤ K ↔
      (lowNormalRealSchwartzPoint3Monomial f) ^ 12 ≤
        K * (lowNormalRealSchwartzH3TopDissipation f) ^ 12 := by
  have hDen : 0 < lowNormalRealSchwartz_sharpShapeDenominator f := by
    unfold lowNormalRealSchwartz_sharpShapeDenominator
    rw [h0, h3]
    positivity
  have hIdentity :
      lowNormalRealSchwartz_sharpShapeDenominator f =
        (lowNormalRealSchwartzH3TopDissipation f) ^ 12 := by
    unfold lowNormalRealSchwartz_sharpShapeDenominator
    rw [h0, h3]
    ring
  unfold lowNormalRealSchwartz_sharpShapeRatio
  rw [(div_le_iff₀ hDen)]
  rw [hIdentity]

/-- Every nonnegative proposed global critical-half coefficient imposes
the sharp factor-two necessary quotient threshold on EVERY solenoidal
unit-endpoint profile. If D = 0, the ratio equals zero by definition,
so no separate D positivity hypothesis is necessary. -/
theorem lowNormalRealSchwartz_uniform_forces_unitEndpoints_ratioBound
    (C : ℝ) (hC : 0 ≤ C)
    (hUniform : ∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      lowNormalRealSchwartzPoint3Monomial g ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy g) *
          lowNormalRealSchwartzH3TopDissipation g) :
    ∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      lowNormalRealSchwartzH3Energy0 g = 1 →
      lowNormalRealSchwartzH3Energy3 g = 1 →
      lowNormalRealSchwartz_sharpShapeRatio g ≤ (2 * C) ^ 12 := by
  intro g hDiv h0 h3
  by_cases hz : lowNormalRealSchwartzH3TopDissipation g = 0
  · have hRatioZero : lowNormalRealSchwartz_sharpShapeRatio g = 0 := by
      unfold lowNormalRealSchwartz_sharpShapeRatio
        lowNormalRealSchwartz_sharpShapeDenominator
      rw [hz]
      norm_num
    rw [hRatioZero]
    positivity
  · have hD : 0 < lowNormalRealSchwartzH3TopDissipation g :=
      lt_of_le_of_ne (lowNormalRealSchwartzH3TopDissipation_nonneg g)
        (Ne.symm hz)
    exact lowNormalRealSchwartz_positiveEndpoints_uniform_bounds_shapeRatio
      C hC g hDiv (by rw [h0]; norm_num) (by rw [h3]; norm_num)
      hD hUniform

/-- A normalized solenoidal Schwartz witness with ratio strictly greater
than the necessary threshold rules out the proposed global coefficient.
The existence of such a witness remains an independent analytic question. -/
theorem lowNormalRealSchwartz_unitEndpoints_ratioExcess_rulesOut_uniform
    (C : ℝ) (hC : 0 ≤ C)
    (g : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal g)
    (h0 : lowNormalRealSchwartzH3Energy0 g = 1)
    (h3 : lowNormalRealSchwartzH3Energy3 g = 1)
    (hRatio : (2 * C) ^ 12 < lowNormalRealSchwartz_sharpShapeRatio g) :
    ¬ (∀ f : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal f →
      lowNormalRealSchwartzPoint3Monomial f ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy f) *
          lowNormalRealSchwartzH3TopDissipation f) := by
  intro hUniform
  have hBound := lowNormalRealSchwartz_uniform_forces_unitEndpoints_ratioBound
    C hC hUniform g hDiv h0 h3
  exact (not_lt_of_ge hBound) hRatio

end
end PrimeTensor.FirstMonomialTriad
