import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSharpBalancedObstruction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Canonical positive balance scale and the sign-free obstruction

The previous signed balanced-shape theorem assumes an explicitly supplied
positive scale satisfying scale^6 * E3 = E0. For positive endpoint energies
that scale exists, independently of the PDE and Fourier transforms: it is
(E0 / E3)^(1/6). This file removes the supplied-scale hypothesis from the
sharp necessary condition and obstruction criterion.

The top endpoint E3 is assumed strictly positive. Positivity of E3 from a
nonzero physical Schwartz profile is a separate analytic statement, not
silently inferred here. No uniform critical-half constant or obstructing
Schwartz witness is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeCanonicalBalance (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every positive pair of endpoint energies admits an actual positive
sixth-root balance scale, with no preselected witness. -/
theorem criticalHalf_positiveEndpoints_exist_balanceScale
    (E0 E3 : ℝ) (hE0 : 0 < E0) (hE3 : 0 < E3) :
    ∃ scale : ℝ, 0 < scale ∧ scale ^ 6 * E3 = E0 := by
  let ratio : ℝ := E0 / E3
  have hr : 0 < ratio := div_pos hE0 hE3
  let scale : ℝ := ratio ^ ((6 : ℕ) : ℝ)⁻¹
  have hs : 0 < scale := Real.rpow_pos_of_pos hr _
  have hp : scale ^ 6 = ratio := by
    change (ratio ^ ((6 : ℕ) : ℝ)⁻¹) ^ 6 = ratio
    exact Real.rpow_inv_natCast_pow hr.le (by norm_num : (6 : ℕ) ≠ 0)
  refine ⟨scale, hs, ?_⟩
  rw [hp]
  change E0 / E3 * E3 = E0
  exact div_mul_cancel₀ E0 (ne_of_gt hE3)

/-- The exact coefficient-one analytic interpolation gives the sharp
sign-free shape bound for EVERY positive-endpoint solenoidal Schwartz
profile, without an independent balancing-scale assumption. -/
theorem lowNormalRealSchwartz_positiveEndpoints_uniform_forces_sharpBound
    (C : ℝ) (hC : 0 ≤ C)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hE3 : 0 < lowNormalRealSchwartzH3Energy3 f)
    (hUniform : ∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      lowNormalRealSchwartzPoint3Monomial g ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy g) *
          lowNormalRealSchwartzH3TopDissipation g) :
    (lowNormalRealSchwartzPoint3Monomial f) ^ 12 ≤
      (2 * C) ^ 12 * (lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
        (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
          lowNormalRealSchwartzH3Energy3 f := by
  obtain ⟨scale, hs, hBalance⟩ :=
    criticalHalf_positiveEndpoints_exist_balanceScale
      (lowNormalRealSchwartzH3Energy0 f)
      (lowNormalRealSchwartzH3Energy3 f) hE0 hE3
  by_contra hNot
  have hStrict :
      (2 * C) ^ 12 * (lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
          (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
          lowNormalRealSchwartzH3Energy3 f <
        (lowNormalRealSchwartzPoint3Monomial f) ^ 12 :=
    lt_of_not_ge hNot
  have hExcess :
      0 < lowNormalRealSchwartz_criticalHalfBalancedExcess (2 * C) f := by
    unfold lowNormalRealSchwartz_criticalHalfBalancedExcess
    exact sub_pos.mpr hStrict
  exact (lowNormalRealSchwartz_sharpBalancedExcess_rulesOut_uniform
    C hC scale hs f hDiv hE0 hBalance hExcess) hUniform

/-- The prior sign-free obstruction is now independent of the *choice* of
scale: positive E0 and E3 construct it canonically. -/
theorem lowNormalRealSchwartz_positiveEndpoints_sharpExcess_rulesOut_uniform
    (C : ℝ) (hC : 0 ≤ C)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hE3 : 0 < lowNormalRealSchwartzH3Energy3 f)
    (hExcess : 0 < lowNormalRealSchwartz_criticalHalfBalancedExcess
      (2 * C) f) :
    ¬ (∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      lowNormalRealSchwartzPoint3Monomial g ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy g) *
          lowNormalRealSchwartzH3TopDissipation g) := by
  obtain ⟨scale, hs, hBalance⟩ :=
    criticalHalf_positiveEndpoints_exist_balanceScale
      (lowNormalRealSchwartzH3Energy0 f)
      (lowNormalRealSchwartzH3Energy3 f) hE0 hE3
  exact lowNormalRealSchwartz_sharpBalancedExcess_rulesOut_uniform
    C hC scale hs f hDiv hE0 hBalance hExcess

/-- The shape-free condition is an explicit dimensionless quotient if the
actual fourth-order dissipation is also positive. Its fixed factor is
(2*C)^12, not the previous factor incurred by axiswise Cauchy. -/
theorem lowNormalRealSchwartz_positiveEndpoints_uniform_bounds_shapeRatio
    (C : ℝ) (hC : 0 ≤ C)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hE3 : 0 < lowNormalRealSchwartzH3Energy3 f)
    (hD : 0 < lowNormalRealSchwartzH3TopDissipation f)
    (hUniform : ∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      lowNormalRealSchwartzPoint3Monomial g ≤
        C * Real.sqrt (lowNormalRealSchwartzH3Energy g) *
          lowNormalRealSchwartzH3TopDissipation g) :
    (lowNormalRealSchwartzPoint3Monomial f) ^ 12 /
      ((lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
        (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
          lowNormalRealSchwartzH3Energy3 f) ≤ (2 * C) ^ 12 := by
  have hBound := lowNormalRealSchwartz_positiveEndpoints_uniform_forces_sharpBound
    C hC f hDiv hE0 hE3 hUniform
  have hDen : 0 <
      (lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
        (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
          lowNormalRealSchwartzH3Energy3 f := by
    positivity
  apply (div_le_iff₀ hDen).2
  calc
    (lowNormalRealSchwartzPoint3Monomial f) ^ 12 ≤
        (2 * C) ^ 12 * (lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
          (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
          lowNormalRealSchwartzH3Energy3 f := hBound
    _ = (2 * C) ^ 12 *
        ((lowNormalRealSchwartzH3TopDissipation f) ^ 12 *
          (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
            lowNormalRealSchwartzH3Energy3 f) := by ring

end
end PrimeTensor.FirstMonomialTriad
