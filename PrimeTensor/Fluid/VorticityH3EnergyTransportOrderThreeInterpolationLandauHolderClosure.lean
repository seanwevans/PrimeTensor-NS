import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationLandauNormBridge
import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationLandauAlgebra

/-!
# Third-order H³ interpolation: Landau-to-Hölder closure

The analytic Landau estimate is now green, and the real/ENNReal norm bridge is
green.  This file joins those layers to the pre-existing
`Holder244ProductBound`.

There are two steps:

1. Convert a real three-factor estimate

       2 * ‖f‖₂ * ‖g‖₄ * ‖q‖₄ ≤ R

   into the ENNReal product bound consumed by the Hölder pairing theorem.

2. Apply `landau_three_factor_algebra` to obtain that real estimate from the
   two Landau L⁴ bounds and the three D³ L² energy contributions.

No PDE-specific derivative bookkeeping occurs here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable local instance axisFintypeH3LandauHolderClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3EnergyDerivative d

noncomputable local instance point3MeasureSpaceH3LandauHolderClosure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3EnergyDerivative Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
A finite real `2-4-4` norm product bound implies the exact ENNReal
`Holder244ProductBound` used by the existing pairing layer.
-/
theorem holder244ProductBound_of_real_norm_product
    {f g q : ScalarField3}
    {R : ℝ}
    (
      hf2 :
        MeasureTheory.MemLp
          f
          (ENNReal.ofReal 2)
          volume
    )
    (
      hg4 :
        MeasureTheory.MemLp
          g
          (ENNReal.ofReal 4)
          volume
    )
    (
      hq4 :
        MeasureTheory.MemLp
          q
          (ENNReal.ofReal 4)
          volume
    )
    (
      hProduct :
        2
          * landauL2 f
          * landauL4 g
          * landauL4 q
          ≤ R
    ) :
    Holder244ProductBound f g q R := by

  refine
    ⟨
      hf2.aemeasurable.enorm,
      hg4.aemeasurable.enorm,
      hq4.aemeasurable.enorm,
      ?_
    ⟩

  rw [
    realLpEnorm_two_eq_ofReal_landauL2 hf2,
    realLpEnorm_four_eq_ofReal_landauL4 hg4,
    realLpEnorm_four_eq_ofReal_landauL4 hq4
  ]

  have hA :
      0 ≤ landauL2 f :=
    landauL2_nonneg f

  have hG :
      0 ≤ landauL4 g :=
    landauL4_nonneg g

  have hQ :
      0 ≤ landauL4 q :=
    landauL4_nonneg q

  have hTwo :
      ‖(2 : ℝ)‖ₑ
        =
      ENNReal.ofReal (2 : ℝ) := by
    calc
      ‖(2 : ℝ)‖ₑ
          =
        ENNReal.ofReal ‖(2 : ℝ)‖ :=
          (ofReal_norm (2 : ℝ)).symm
      _ =
        ENNReal.ofReal (2 : ℝ) := by
          norm_num

  rw [hTwo]

  have hPacked :
      ENNReal.ofReal (2 : ℝ)
          *
        (
          ENNReal.ofReal (landauL2 f)
            *
          (
            ENNReal.ofReal (landauL4 g)
              *
            ENNReal.ofReal (landauL4 q)
          )
        )
        =
      ENNReal.ofReal
        (
          2
            *
          (
            landauL2 f
              *
            (
              landauL4 g
                *
              landauL4 q
            )
          )
        ) := by

    rw [
      ← ENNReal.ofReal_mul hG,
      ← ENNReal.ofReal_mul hA,
      ← ENNReal.ofReal_mul
        (by norm_num : 0 ≤ (2 : ℝ))
    ]

  rw [hPacked]

  apply ENNReal.ofReal_le_ofReal

  simpa only [mul_assoc] using hProduct

/--
The scalar Landau algebra directly yields a `Holder244ProductBound`.

`B` and `C` are the L² magnitudes of the two third derivatives controlling
the D² factors `g` and `q`.
-/
theorem holder244ProductBound_of_landau_algebra
    {f g q : ScalarField3}
    {B C h E : ℝ}
    (
      hf2 :
        MeasureTheory.MemLp
          f
          (ENNReal.ofReal 2)
          volume
    )
    (
      hg4 :
        MeasureTheory.MemLp
          g
          (ENNReal.ofReal 4)
          volume
    )
    (
      hq4 :
        MeasureTheory.MemLp
          q
          (ENNReal.ofReal 4)
          volume
    )
    (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (hh : 0 ≤ h)
    (
      hG2 :
        landauL4 g ^ 2
          ≤
        3 * h * B
    )
    (
      hQ2 :
        landauL4 q ^ 2
          ≤
        3 * h * C
    )
    (
      hEnergy :
        landauL2 f ^ 2
          + B ^ 2
          + C ^ 2
          ≤ E
    ) :
    Holder244ProductBound
      f g q
      (3 * h * E) := by

  apply
    holder244ProductBound_of_real_norm_product
      hf2 hg4 hq4

  exact
    landau_three_factor_algebra
      (landauL2_nonneg f)
      hB
      hC
      (landauL4_nonneg g)
      (landauL4_nonneg q)
      hh
      hG2
      hQ2
      hEnergy

/--
A Landau inequality in the already-proved `landauL4Squared` form can be
rewritten into the square form expected by the scalar closure.
-/
lemma landauL4_sq_le_of_landauL4Squared_le
    {g : ScalarField3}
    {R : ℝ}
    (
      h :
        landauL4Squared g ≤ R
    ) :
    landauL4 g ^ 2 ≤ R := by

  rw [pow_two, landauL4_mul_self]

  exact h

end Euclidean
end Bridge
end PrimeTensor
