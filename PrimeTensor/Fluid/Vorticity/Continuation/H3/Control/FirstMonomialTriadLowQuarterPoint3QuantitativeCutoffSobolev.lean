import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzQuarticL2L6
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Whole.Space.Sobolev

/-!
# Quantitative radius-dependent Sobolev control on the true Point3 carrier

The existing whole-space `C¹ ∩ H¹ → L⁶` proof bounds cutoff derivatives by
`‖Dg‖ + C|g|`, then uses Fatou to conclude membership. That is sufficient
for `MemLp` but *not* the homogeneous, profile-independent estimate needed
by the classical critical-half Gagliardo–Nirenberg argument.

The already proved cutoff scaling lemma is stronger: for every R>0,

  ‖D(χ_R g)(x)‖ ≤ ‖Dg(x)‖ + (C/R)|g(x)|.

We retain the exact `C/R` term in the quantitative Sobolev inequality

  ‖χ_R g‖₆ ≤ S ‖ ‖Dg‖ + (C/R)|g| ‖₂,

where C and S do NOT depend on R or g; C comes from the project's cutoff,
and S is Mathlib's 3D compact-support Sobolev constant. All expressions are
the genuine `Point3` norms, with no new analytic hypothesis and no axiom.

Passing to R → ∞ and removing the remainder is the NEXT analytic task; this
module does not assert an unconditional homogeneous Sobolev bound yet.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3CriticalCutoffSobolev
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual cutoff derivative estimate with its vanishing, radius-dependent
error rather than the old radius-independent bound `C |g|`. The SAME constant
works for all radii and all fields with a spatial `C¹` derivative. -/
theorem exists_uniform_radius_cutoff_fderiv_majorant
    {g : ScalarField3} (hC1 : SpatialC1 g) :
    ∃ C : ℝ≥0, ∀ {R : ℝ} (hR : 0 < R) (x : Point3),
      ‖fderiv ℝ (h3LandauCutoffField R hR g) x‖ ≤
        ‖fderiv ℝ g x‖ + ((C : ℝ) / R) * |g x| := by
  obtain ⟨C, hCutoff⟩ :=
    exists_uniform_norm_fderiv_h3LandauCutoffBump_le_div
  refine ⟨C, ?_⟩
  intro R hR x
  have hProduct := norm_fderiv_h3LandauCutoffField_le hR hC1 x
  have hCutoffBound := hCutoff hR x
  have hError :
      |g x| *
        ‖fderiv ℝ (fun y : Point3 => h3LandauCutoffBump R hR y) x‖ ≤
      |g x| * ((C : ℝ) / R) :=
    mul_le_mul_of_nonneg_left hCutoffBound (abs_nonneg _)
  calc
    ‖fderiv ℝ (h3LandauCutoffField R hR g) x‖ ≤
        ‖fderiv ℝ g x‖ + |g x| *
          ‖fderiv ℝ (fun y : Point3 => h3LandauCutoffBump R hR y) x‖ :=
      hProduct
    _ ≤ ‖fderiv ℝ g x‖ + |g x| * ((C : ℝ) / R) :=
      add_le_add_right hError _
    _ = ‖fderiv ℝ g x‖ + ((C : ℝ) / R) * |g x| := by ring

/-- Quantitative compact-support Sobolev bound with the exact shrinking
cutoff error. In contrast to the previous `MemLp` theorem, the SAME
radius-independent constants are displayed and the dependence on R is
explicit. Nothing about Navier–Stokes dynamics or incompressibility is used.
-/
theorem exists_uniform_radius_cutoff_quantitative_L6
    {g : ScalarField3}
    (hC1 : SpatialC1 g)
    (hg2 : MemLp g (ENNReal.ofReal 2) volume)
    (hDg2 : MemLp (fun x : Point3 => fderiv ℝ g x)
      (ENNReal.ofReal 2) volume) :
    ∃ C : ℝ≥0, ∀ {R : ℝ} (hR : 0 < R),
      eLpNorm (h3LandauCutoffField R hR g)
          (ENNReal.ofReal 6) volume ≤
        ((MeasureTheory.SNormLESNormFDerivOfEqConst
          ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
          eLpNorm
            (fun x : Point3 =>
              ‖fderiv ℝ g x‖ + ((C : ℝ) / R) * |g x|)
            (ENNReal.ofReal 2) volume := by
  obtain ⟨C, hRadius⟩ :=
    exists_uniform_radius_cutoff_fderiv_majorant hC1
  refine ⟨C, ?_⟩
  intro R hR
  let majorant : Point3 → ℝ :=
    fun x => ‖fderiv ℝ g x‖ + ((C : ℝ) / R) * |g x|
  have hCoeff : 0 ≤ (C : ℝ) / R :=
    div_nonneg C.coe_nonneg hR.le
  have hMajorantNonneg (x : Point3) : 0 ≤ majorant x := by
    dsimp [majorant]
    exact add_nonneg (norm_nonneg _) (mul_nonneg hCoeff (abs_nonneg _))
  have hMajorantMemLp :
      MemLp majorant (ENNReal.ofReal 2) volume := by
    have hDgNorm : MemLp (fun x : Point3 => ‖fderiv ℝ g x‖)
        (ENNReal.ofReal 2) volume := hDg2.norm
    have hgAbs : MemLp (fun x : Point3 => |g x|)
        (ENNReal.ofReal 2) volume := by
      simpa [Real.norm_eq_abs] using hg2.norm
    have hgScaled : MemLp (fun x : Point3 => ((C : ℝ) / R) * |g x|)
        (ENNReal.ofReal 2) volume :=
      hgAbs.const_mul ((C : ℝ) / R)
    exact hDgNorm.add hgScaled
  have hDerivativeBound :
      eLpNorm (fun x : Point3 =>
          fderiv ℝ (h3LandauCutoffField R hR g) x)
          (ENNReal.ofReal 2) volume ≤
        eLpNorm majorant (ENNReal.ofReal 2) volume := by
    apply eLpNorm_mono_ae
    filter_upwards with x
    have hRaw := hRadius hR x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hMajorantNonneg x)] using hRaw
  have hSobolev :=
    MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
      (μ := (volume : Measure Point3))
      (F := ℝ)
      (h3LandauCutoffField_spatialC1 hR hC1)
      (h3LandauCutoffField_hasCompactSupport hR g)
      (p := (2 : ℝ≥0))
      (p' := (6 : ℝ≥0))
      (by norm_num)
      (by rw [point3_finrank_eq_three_landau]; norm_num)
      (by rw [point3_finrank_eq_three_landau]; norm_num)
  have hSobolev' :
      eLpNorm (h3LandauCutoffField R hR g)
          (ENNReal.ofReal 6) volume ≤
        ((MeasureTheory.SNormLESNormFDerivOfEqConst
          ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
          eLpNorm (fun x : Point3 =>
            fderiv ℝ (h3LandauCutoffField R hR g) x)
            (ENNReal.ofReal 2) volume := by
    simpa using hSobolev
  calc
    eLpNorm (h3LandauCutoffField R hR g)
        (ENNReal.ofReal 6) volume ≤
      ((MeasureTheory.SNormLESNormFDerivOfEqConst
        ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fun x : Point3 =>
          fderiv ℝ (h3LandauCutoffField R hR g) x)
          (ENNReal.ofReal 2) volume := hSobolev'
    _ ≤ ((MeasureTheory.SNormLESNormFDerivOfEqConst
        ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
          eLpNorm majorant (ENNReal.ofReal 2) volume := by
      gcongr
    _ = _ := rfl

end
end Euclidean
end Bridge
end PrimeTensor
