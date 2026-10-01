import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Closure
import PrimeTensor.Fluid.Vorticity.H3.Axis.Sum
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# Compact-support anchor for the whole-space Landau Sobolev frontier

`WholeSpaceC1FDerivL2ToL6` is the standard whole-space endpoint

    C¹ ∩ H¹(ℝ³) -> L⁶(ℝ³).

Mathlib already proves the Gagliardo--Nirenberg--Sobolev estimate for
compactly-supported continuously differentiable functions on a finite-
dimensional real normed space equipped with Haar measure.

This file specializes that theorem to PrimeTensor's concrete physical carrier
`Point3`.  It deliberately stops before the only genuinely missing step:
removing compact support by cutoff approximation.

Thus the future whole-space proof can focus entirely on a cutoff family and
passage to the limit, rather than simultaneously debugging the Sobolev API,
the dimension computation, and the `MemLp` endpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3LandauCompactSupportSobolev
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3LandauCompactSupportSobolev :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3LandauCompactSupportSobolev Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- PrimeTensor's concrete physical coordinate carrier has real dimension
three. -/
theorem point3_finrank_eq_three_landau :
    Module.finrank ℝ Point3 = 3 := by
  change
    Module.finrank ℝ
      (∀ _ : PrimeTensor.Axis Depth.three, ℝ)
      =
    3

  rw [Module.finrank_pi_fintype]

  simpa using
    (axis_sum_three
      (fun _ : PrimeTensor.Axis Depth.three => (1 : ℕ)))

/-- Compact-support form of the `C¹ ∩ H¹ -> L⁶` endpoint needed by the Landau
interpolation argument.

The `L²` hypothesis on the field itself is unnecessary in the compact-support
case; the Gagliardo--Nirenberg--Sobolev estimate controls the `L⁶` norm directly
by the `L²` norm of the Fréchet derivative. -/
theorem memLp_six_of_spatialC1_of_hasCompactSupport_of_fderiv_memLp_two
    {g : ScalarField3}
    (hC1 : SpatialC1 g)
    (hSupport : HasCompactSupport g)
    (hFDeriv2 :
      MeasureTheory.MemLp
        (fun x : Point3 => fderiv ℝ g x)
        (ENNReal.ofReal 2)
        volume) :
    MeasureTheory.MemLp
      g
      (ENNReal.ofReal 6)
      volume := by
  have hSobolev :=
    MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
      (μ := (volume : Measure Point3))
      (F := ℝ)
      hC1
      hSupport
      (p := (2 : ℝ≥0))
      (p' := (6 : ℝ≥0))
      (by norm_num)
      (by
        rw [point3_finrank_eq_three_landau]
        norm_num)
      (by
        rw [point3_finrank_eq_three_landau]
        norm_num)

  have hFDerivTop :
      eLpNorm
          (fun x : Point3 => fderiv ℝ g x)
          (ENNReal.ofReal 2)
          volume
        <
      ∞ :=
    hFDeriv2.eLpNorm_lt_top

  unfold MeasureTheory.MemLp

  constructor

  · exact hC1.continuous.aestronglyMeasurable

  · calc
      eLpNorm g (ENNReal.ofReal 6) volume
        ≤
      ((MeasureTheory.SNormLESNormFDerivOfEqConst
          ℝ
          (volume : Measure Point3)
          (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞)
        *
      eLpNorm
        (fun x : Point3 => fderiv ℝ g x)
        (ENNReal.ofReal 2)
        volume := by
          simpa using hSobolev

      _ < ∞ := by
        exact
          ENNReal.mul_lt_top
            (by simp)
            hFDerivTop

end

end Euclidean
end Bridge
end PrimeTensor
