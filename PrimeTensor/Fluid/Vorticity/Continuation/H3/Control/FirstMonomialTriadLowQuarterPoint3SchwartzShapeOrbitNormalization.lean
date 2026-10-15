import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzCanonicalBalanceScale

/-!
# The intrinsic Schwartz critical-half shape ratio and its normalized orbit

The previous files proved the exact spatial and amplitude homogeneities of the
signed 243-slot monomial, fourth-order dissipation, and the zero/third endpoint
masses. Their exponents cancel *exactly* in the critical-half shape quotient.

This module proves genuine invariance of that quotient under both changes of
units. It then constructs a representative of every positive-endpoint real
Schwartz velocity having **both** E0=1 and E3=1, by one positive spatial
dilation followed by one positive amplitude rescaling. The solenoidal class is
preserved. The normalized class is not asserted compact, and no universal
nonlinear bound or counterexample is inferred from these identities.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeShapeOrbit (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact homogeneous denominator, using the complete 243-slot
fourth-order dissipation and the actual endpoint Schwartz energy blocks. -/
noncomputable def lowNormalRealSchwartz_sharpShapeDenominator
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  (lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
    (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
      lowNormalRealSchwartzH3Energy3 f

/-- A dimensionless, sign-insensitive ratio on the positive-denominator
Schwartz class. Division by zero has the standard real-field convention;
our applications state strict denominator positivity explicitly. -/
noncomputable def lowNormalRealSchwartz_sharpShapeRatio
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  (lowNormalRealSchwartzPoint3Monomial f) ^ 12 /
    lowNormalRealSchwartz_sharpShapeDenominator f

/-- Pure scalar cancellation, including the zero-denominator case. -/
private theorem lowNormal_shape_ratio_cancel
    (s n d : ℝ) (hs : s ≠ 0) :
    (s * n) / (s * d) = n / d := by
  by_cases hd : d = 0
  · simp [hd]
  · field_simp [hs, hd]

/-- The exact denominator has total amplitude degree 36, matching M^12. -/
theorem lowNormalRealSchwartz_sharpShapeDenominator_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_sharpShapeDenominator
        (fun j : A3 => a • f j) =
      a ^ 36 * lowNormalRealSchwartz_sharpShapeDenominator f := by
  unfold lowNormalRealSchwartz_sharpShapeDenominator
  rw [lowNormalRealSchwartzH3TopDissipation_real_smul,
    lowNormalRealSchwartzH3Energy0_real_smul,
    lowNormalRealSchwartzH3Energy3_real_smul]
  ring

/-- The denominator has spatial degree 48, exactly matching M^12. -/
theorem lowNormalRealSchwartz_sharpShapeDenominator_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_sharpShapeDenominator
        (lowNormalSchwartzVelocityDilation scale hscale f) =
      scale ^ 48 * lowNormalRealSchwartz_sharpShapeDenominator f := by
  have hs : scale ≠ 0 := ne_of_gt hscale
  have hCoeff :
      ((scale ^ 8 * (scale ^ 3)⁻¹) ^ 12 *
        ((scale ^ 3)⁻¹) ^ 5) *
        (scale ^ 6 * (scale ^ 3)⁻¹) = scale ^ 48 := by
    field_simp [hs]
  unfold lowNormalRealSchwartz_sharpShapeDenominator
  rw [lowNormalRealSchwartzH3TopDissipation_dilation,
    lowNormalRealSchwartzH3Energy0_dilation,
    lowNormalRealSchwartzH3Energy3_dilation]
  let D : ℝ := lowNormalRealSchwartzH3TopDissipation f
  let E0 : ℝ := lowNormalRealSchwartzH3Energy0 f
  let E3 : ℝ := lowNormalRealSchwartzH3Energy3 f
  change ((scale ^ 8 * (scale ^ 3)⁻¹) * D) ^ 12 *
    ((scale ^ 3)⁻¹ * E0) ^ 5 *
    ((scale ^ 6 * (scale ^ 3)⁻¹) * E3) =
      scale ^ 48 * (D ^ 12 * E0 ^ 5 * E3)
  calc
    _ = (((scale ^ 8 * (scale ^ 3)⁻¹) ^ 12 *
          ((scale ^ 3)⁻¹) ^ 5) *
          (scale ^ 6 * (scale ^ 3)⁻¹)) *
          (D ^ 12 * E0 ^ 5 * E3) := by ring
    _ = scale ^ 48 * (D ^ 12 * E0 ^ 5 * E3) := by rw [hCoeff]

/-- The shape quotient is invariant under all nonzero real amplitudes,
including negative amplitudes that reverse the cubic monomial's sign. -/
theorem lowNormalRealSchwartz_sharpShapeRatio_real_smul
    (a : ℝ) (ha : a ≠ 0)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_sharpShapeRatio
      (fun j : A3 => a • f j) =
    lowNormalRealSchwartz_sharpShapeRatio f := by
  unfold lowNormalRealSchwartz_sharpShapeRatio
  rw [lowNormalRealSchwartzPoint3Monomial_real_smul,
    lowNormalRealSchwartz_sharpShapeDenominator_real_smul]
  have hpow : ((a ^ 3) * lowNormalRealSchwartzPoint3Monomial f) ^ 12 =
      a ^ 36 * (lowNormalRealSchwartzPoint3Monomial f) ^ 12 := by ring
  rw [hpow]
  exact lowNormal_shape_ratio_cancel _ _ _ (pow_ne_zero 36 ha)

/-- The shape quotient is invariant under every positive physical
three-dimensional isotropic spatial dilation. -/
theorem lowNormalRealSchwartz_sharpShapeRatio_dilation
    (scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartz_sharpShapeRatio
      (lowNormalSchwartzVelocityDilation scale hscale f) =
    lowNormalRealSchwartz_sharpShapeRatio f := by
  unfold lowNormalRealSchwartz_sharpShapeRatio
  rw [lowNormalRealSchwartzPoint3Monomial_dilation,
    lowNormalRealSchwartz_sharpShapeDenominator_dilation]
  have hpow : ((scale ^ 4) * lowNormalRealSchwartzPoint3Monomial f) ^ 12 =
      scale ^ 48 * (lowNormalRealSchwartzPoint3Monomial f) ^ 12 := by ring
  rw [hpow]
  exact lowNormal_shape_ratio_cancel _ _ _
    (pow_ne_zero 48 (ne_of_gt hscale))

/-- An elementary two-parameter normalization of the endpoints. The
spatial parameter first makes E0 and E3 equal; amplitude then makes both
unit mass. No third-order nondegeneracy claim is smuggled in here. -/
private theorem criticalHalf_positiveEndpoints_exist_unitScales
    (E0 E3 : ℝ) (hE0 : 0 < E0) (hE3 : 0 < E3) :
    ∃ scale : ℝ, ∃ hscale : 0 < scale,
      ∃ a : ℝ, 0 < a ∧
        a ^ 2 * ((scale ^ 3)⁻¹ * E0) = 1 ∧
        a ^ 2 * ((scale ^ 6 * (scale ^ 3)⁻¹) * E3) = 1 := by
  obtain ⟨scale, hscale, hBalance⟩ :=
    criticalHalf_positiveEndpoints_exist_balanceScale E0 E3 hE0 hE3
  let B : ℝ := (scale ^ 3)⁻¹ * E0
  have hB : 0 < B :=
    mul_pos (inv_pos.mpr (pow_pos hscale 3)) hE0
  let a : ℝ := (Real.sqrt B)⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.2 hB)
  have hroot : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB.le
  have hunit : a ^ 2 * B = 1 := by
    dsimp only [a]
    rw [inv_pow, hroot]
    exact inv_mul_cancel₀ (ne_of_gt hB)
  have hOther : (scale ^ 6 * (scale ^ 3)⁻¹) * E3 = B := by
    calc
      _ = (scale ^ 3)⁻¹ * (scale ^ 6 * E3) := by ring
      _ = B := by rw [hBalance]
  refine ⟨scale, hscale, a, ha, ?_, ?_⟩
  · exact hunit
  · rw [hOther]
    exact hunit

/-- Every positive-endpoint real Schwartz velocity admits an actual
Schwartz representative with E0=E3=1, preserving the intrinsic shape ratio.
Incompressibility is also preserved if it held for the original velocity. -/
theorem lowNormalRealSchwartz_positiveEndpoints_exist_unitOrbitRepresentative
    (f : A3 → SchwartzMap V3 ℝ)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hE3 : 0 < lowNormalRealSchwartzH3Energy3 f) :
    ∃ scale : ℝ, ∃ hscale : 0 < scale,
      ∃ a : ℝ, 0 < a ∧
        let g : A3 → SchwartzMap V3 ℝ :=
          fun j => a • (lowNormalSchwartzVelocityDilation scale hscale f j)
        lowNormalRealSchwartzH3Energy0 g = 1 ∧
        lowNormalRealSchwartzH3Energy3 g = 1 ∧
        lowNormalRealSchwartz_sharpShapeRatio g =
          lowNormalRealSchwartz_sharpShapeRatio f := by
  obtain ⟨scale, hscale, a, ha, hUnit0, hUnit3⟩ :=
    criticalHalf_positiveEndpoints_exist_unitScales
      (lowNormalRealSchwartzH3Energy0 f)
      (lowNormalRealSchwartzH3Energy3 f) hE0 hE3
  refine ⟨scale, hscale, a, ha, ?_, ?_, ?_⟩
  · rw [lowNormalRealSchwartzH3Energy0_real_smul,
        lowNormalRealSchwartzH3Energy0_dilation]
    exact hUnit0
  · rw [lowNormalRealSchwartzH3Energy3_real_smul,
        lowNormalRealSchwartzH3Energy3_dilation]
    exact hUnit3
  · rw [lowNormalRealSchwartz_sharpShapeRatio_real_smul a
          (ne_of_gt ha),
        lowNormalRealSchwartz_sharpShapeRatio_dilation scale hscale f]

/-- Within the positive-endpoint class, strict excess of the dimensionless
ratio rules out the proposed global solenoidal critical-half coefficient.
No witness profile is asserted to exist. -/
theorem lowNormalRealSchwartz_sharpShapeRatio_excess_rulesOut_uniform
    (C : ℝ) (hC : 0 ≤ C)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hE3 : 0 < lowNormalRealSchwartzH3Energy3 f)
    (hD : 0 < lowNormalRealSchwartzH3TopDissipation f)
    (hRatio : (2 * C) ^ 12 < lowNormalRealSchwartz_sharpShapeRatio f) :
    ¬ (∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      lowNormalRealSchwartzPoint3Monomial g ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy g) *
          lowNormalRealSchwartzH3TopDissipation g) := by
  have hDen : 0 < lowNormalRealSchwartz_sharpShapeDenominator f := by
    unfold lowNormalRealSchwartz_sharpShapeDenominator
    positivity
  have hStrict :
      (2 * C) ^ 12 * lowNormalRealSchwartz_sharpShapeDenominator f <
        (lowNormalRealSchwartzPoint3Monomial f) ^ 12 := by
    exact (lt_div_iff₀ hDen).mp hRatio
  have hExcess :
      0 < lowNormalRealSchwartz_criticalHalfBalancedExcess (2 * C) f := by
    unfold lowNormalRealSchwartz_criticalHalfBalancedExcess
    apply sub_pos.mpr
    calc
      (2 * C) ^ 12 * (lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
          (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
            lowNormalRealSchwartzH3Energy3 f =
        (2 * C) ^ 12 * lowNormalRealSchwartz_sharpShapeDenominator f := by
          unfold lowNormalRealSchwartz_sharpShapeDenominator
          ring
      _ < (lowNormalRealSchwartzPoint3Monomial f) ^ 12 := hStrict
  exact lowNormalRealSchwartz_positiveEndpoints_sharpExcess_rulesOut_uniform
    C hC f hDiv hE0 hE3 hExcess

end
end PrimeTensor.FirstMonomialTriad
