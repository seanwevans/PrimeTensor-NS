import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Cutoff.Derivative
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Scaling of the Landau cutoff derivative

The cutoff constructed in `Cutoff` has inner radius `R` and outer radius `2R`.
Mathlib's `ContDiffBump` implementation normalizes its argument by `rIn⁻¹`,
so this family is exactly a dilation of the unit cutoff:

    χ_R(x) = χ_1(R⁻¹ x).

The generic `fderiv_comp_smul` theorem then gives

    Dχ_R(x) = R⁻¹ • Dχ_1(R⁻¹ x).

Since the unit cutoff derivative is globally bounded, there is one constant
`C`, independent of `R`, such that

    ‖Dχ_R(x)‖ ≤ C / R

for every positive radius and every physical point.

This is the quantitative estimate needed for the cutoff error
`g Dχ_R` in the whole-space Sobolev closure.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function
open scoped Topology ContDiff NNReal

noncomputable section

noncomputable local instance axisFintypeH3LandauCutoffScaling
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every positive-radius cutoff is exactly the unit cutoff composed with the
spatial dilation `x ↦ R⁻¹ • x`. -/
theorem h3LandauCutoffBump_eq_unit_smul
    {R : ℝ}
    (hR : 0 < R)
    (x : Point3) :
    h3LandauCutoffBump R hR x
      =
    h3LandauCutoffBump (1 : ℝ) zero_lt_one (R⁻¹ • x) := by
  rw [
    ContDiffBump.apply,
    ContDiffBump.apply
  ]

  simp [
    h3LandauCutoffBump,
    hR.ne',
    div_eq_mul_inv
  ]

/-- Functional form of the cutoff scaling identity. -/
theorem h3LandauCutoffBump_fun_eq_unit_comp_smul
    {R : ℝ}
    (hR : 0 < R) :
    (fun x : Point3 =>
      h3LandauCutoffBump R hR x)
      =
    (fun x : Point3 =>
      h3LandauCutoffBump (1 : ℝ) zero_lt_one (R⁻¹ • x)) := by
  funext x

  exact
    h3LandauCutoffBump_eq_unit_smul
      hR x

/-- Exact derivative scaling of the cutoff family. -/
theorem fderiv_h3LandauCutoffBump_eq_inv_smul_unit
    {R : ℝ}
    (hR : 0 < R)
    (x : Point3) :
    fderiv ℝ
        (fun y : Point3 =>
          h3LandauCutoffBump R hR y)
        x
      =
    R⁻¹
      •
    fderiv ℝ
        (fun y : Point3 =>
          h3LandauCutoffBump (1 : ℝ) zero_lt_one y)
        (R⁻¹ • x) := by
  rw [
    h3LandauCutoffBump_fun_eq_unit_comp_smul
      hR
  ]

  simpa using
    (fderiv_comp_smul
      (𝕜 := ℝ)
      (f :=
        fun y : Point3 =>
          h3LandauCutoffBump (1 : ℝ) zero_lt_one y)
      (x := x)
      R⁻¹)

/-- Norm form of the exact derivative scaling identity. -/
theorem norm_fderiv_h3LandauCutoffBump_eq_inv_mul_unit
    {R : ℝ}
    (hR : 0 < R)
    (x : Point3) :
    ‖fderiv ℝ
        (fun y : Point3 =>
          h3LandauCutoffBump R hR y)
        x‖
      =
    R⁻¹
      *
    ‖fderiv ℝ
        (fun y : Point3 =>
          h3LandauCutoffBump (1 : ℝ) zero_lt_one y)
        (R⁻¹ • x)‖ := by
  rw [
    fderiv_h3LandauCutoffBump_eq_inv_smul_unit
      hR x,
    norm_smul,
    Real.norm_eq_abs,
    abs_inv,
    abs_of_pos hR
  ]

/-- A single radius-independent constant controls every cutoff derivative with
the sharp dilation factor `1 / R`. -/
theorem exists_uniform_norm_fderiv_h3LandauCutoffBump_le_div
    :
    ∃ C : ℝ≥0,
      ∀ {R : ℝ}
        (hR : 0 < R)
        (x : Point3),
          ‖fderiv ℝ
              (fun y : Point3 =>
                h3LandauCutoffBump R hR y)
              x‖
            ≤
          (C : ℝ) / R := by
  obtain ⟨C, hC⟩ :=
    exists_norm_fderiv_h3LandauCutoffBump_le
      (R := (1 : ℝ))
      zero_lt_one

  refine ⟨C, ?_⟩

  intro R hR x

  rw [
    norm_fderiv_h3LandauCutoffBump_eq_inv_mul_unit
      hR x
  ]

  have hInvNonneg :
      0 ≤ R⁻¹ :=
    (inv_pos.mpr hR).le

  calc
    R⁻¹
        *
      ‖fderiv ℝ
          (fun y : Point3 =>
            h3LandauCutoffBump (1 : ℝ) zero_lt_one y)
          (R⁻¹ • x)‖
        ≤
      R⁻¹ * (C : ℝ) := by
        exact
          mul_le_mul_of_nonneg_left
            (hC (R⁻¹ • x))
            hInvNonneg

    _ =
      (C : ℝ) / R := by
        rw [div_eq_mul_inv]
        exact mul_comm _ _

end

end Euclidean
end Bridge
end PrimeTensor
