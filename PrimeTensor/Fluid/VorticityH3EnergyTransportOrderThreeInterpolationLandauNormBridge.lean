import Mathlib.MeasureTheory.Integral.Bochner.Basic
import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationLandauCancel

/-!
# Third-order H³ interpolation: real/ENNReal norm bridge

The Landau cancellation theorem is stated with real root-form quantities:

    landauL4Squared g = (∫ g⁴)^(1/2)
    landauL2 dg       = (∫ dg²)^(1/2).

The pre-existing Hölder closure uses `realLpEnorm`, an `ℝ≥0∞`-valued raw
Lp seminorm.  This file proves that, under the corresponding `MemLp`
hypotheses, these are the same quantities.

We also introduce the ordinary real L⁴ norm

    landauL4 g = (∫ g⁴)^(1/4),

and prove

    landauL4 g * landauL4 g = landauL4Squared g.

No PDE content occurs here; this is only a representation bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped ENNReal NNReal

noncomputable local instance axisFintypeH3LandauNormBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3EnergyDerivative d

noncomputable local instance point3MeasureSpaceH3LandauNormBridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3EnergyDerivative Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Pointwise power normalization -/

lemma norm_rpow_two_eq_sq
    (a : ℝ) :
    ‖a‖ ^ (2 : ℝ) = a ^ 2 := by
  simpa only [Real.norm_eq_abs] using
    abs_rpow_two_eq_sq a

lemma abs_rpow_four_eq_pow_four
    (a : ℝ) :
    abs a ^ (4 : ℝ) = a ^ 4 := by
  calc
    abs a ^ (4 : ℝ)
        =
      abs a ^ (4 : ℕ) := by
        exact Real.rpow_natCast (abs a) 4
    _ =
      abs (a ^ 4) := by
        rw [abs_pow]
    _ = a ^ 4 := by
        rw [abs_of_nonneg]
        positivity

lemma norm_rpow_four_eq_pow_four
    (a : ℝ) :
    ‖a‖ ^ (4 : ℝ) = a ^ 4 := by
  simpa only [Real.norm_eq_abs] using
    abs_rpow_four_eq_pow_four a


lemma norm_pow_four_eq_pow_four
    (a : ℝ) :
    ‖a‖ ^ (4 : ℕ) = a ^ 4 := by
  rw [Real.norm_eq_abs, ← abs_pow]
  rw [abs_of_nonneg]
  positivity


lemma abs_pow_four_eq_pow_four
    (a : ℝ) :
    abs a ^ (4 : ℕ) = a ^ 4 := by
  rw [← abs_pow]
  rw [abs_of_nonneg]
  positivity

/-! ## Real L⁴ root form -/

noncomputable def landauL4
    (g : ScalarField3) : ℝ :=
  (
    ∫ x : Point3,
      (g x) ^ 4
  ) ^ (1 / (4 : ℝ))

lemma landauL4_nonneg
    (g : ScalarField3) :
    0 ≤ landauL4 g := by
  unfold landauL4
  exact
    Real.rpow_nonneg
      (quartic_integral_nonneg g)
      _

lemma landauL4_mul_self
    (g : ScalarField3) :
    landauL4 g * landauL4 g
      =
    landauL4Squared g := by

  have hI :
      0 ≤
        ∫ x : Point3,
          (g x) ^ 4 :=
    quartic_integral_nonneg g

  unfold landauL4 landauL4Squared

  rw [
    ← Real.rpow_add_of_nonneg
        hI
        (by norm_num : 0 ≤ (1 / (4 : ℝ)))
        (by norm_num : 0 ≤ (1 / (4 : ℝ)))
  ]

  norm_num

/-! ## `realLpEnorm` = ordinary root form under `MemLp` -/

theorem realLpEnorm_two_eq_ofReal_landauL2
    {f : ScalarField3}
    (hf :
      MeasureTheory.MemLp
        f
        (ENNReal.ofReal 2)
        volume) :
    realLpEnorm volume 2 f
      =
    ENNReal.ofReal (landauL2 f) := by

  have hp0 :
      (ENNReal.ofReal (2 : ℝ)) ≠ 0 := by
    norm_num

  have hpTop :
      (ENNReal.ofReal (2 : ℝ)) ≠ ∞ := by
    exact ENNReal.ofReal_ne_top

  have hFormula :
      MeasureTheory.eLpNorm
          f
          (ENNReal.ofReal 2)
          volume
        =
      ENNReal.ofReal
        (
          (
            ∫ x : Point3,
              ‖f x‖ ^
                (ENNReal.ofReal (2 : ℝ)).toReal
          ) ^
          (ENNReal.ofReal (2 : ℝ)).toReal⁻¹
        ) :=
    MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm
      hp0
      hpTop
      hf

  have hRawEq :
      realLpEnorm volume 2 f
        =
      MeasureTheory.eLpNorm
        f
        (ENNReal.ofReal 2)
        volume := by

    unfold realLpEnorm

    have hELp :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (p := ENNReal.ofReal (2 : ℝ))
        (μ := volume)
        (f := f)
        hp0
        hpTop

    symm
    simpa using hELp

  rw [hRawEq, hFormula]

  unfold landauL2

  congr 1

  norm_num

theorem realLpEnorm_four_eq_ofReal_landauL4
    {f : ScalarField3}
    (hf :
      MeasureTheory.MemLp
        f
        (ENNReal.ofReal 4)
        volume) :
    realLpEnorm volume 4 f
      =
    ENNReal.ofReal (landauL4 f) := by

  have hp0 :
      (ENNReal.ofReal (4 : ℝ)) ≠ 0 := by
    norm_num

  have hpTop :
      (ENNReal.ofReal (4 : ℝ)) ≠ ∞ := by
    exact ENNReal.ofReal_ne_top

  have hFormula :
      MeasureTheory.eLpNorm
          f
          (ENNReal.ofReal 4)
          volume
        =
      ENNReal.ofReal
        (
          (
            ∫ x : Point3,
              ‖f x‖ ^
                (ENNReal.ofReal (4 : ℝ)).toReal
          ) ^
          (ENNReal.ofReal (4 : ℝ)).toReal⁻¹
        ) :=
    MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm
      hp0
      hpTop
      hf

  have hRawEq :
      realLpEnorm volume 4 f
        =
      MeasureTheory.eLpNorm
        f
        (ENNReal.ofReal 4)
        volume := by

    unfold realLpEnorm

    have hELp :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (p := ENNReal.ofReal (4 : ℝ))
        (μ := volume)
        (f := f)
        hp0
        hpTop

    symm
    simpa using hELp

  rw [hRawEq, hFormula]

  unfold landauL4

  congr 1

  norm_num

  have hIntegral :
      (
        ∫ x : Point3,
          abs (f x) ^ (4 : ℕ)
      )
        =
      ∫ x : Point3,
        (f x) ^ 4 := by
    apply integral_congr_ae
    exact
      Filter.Eventually.of_forall
        (fun x : Point3 =>
          abs_pow_four_eq_pow_four (f x))

  rw [hIntegral]

end Euclidean
end Bridge
end PrimeTensor
