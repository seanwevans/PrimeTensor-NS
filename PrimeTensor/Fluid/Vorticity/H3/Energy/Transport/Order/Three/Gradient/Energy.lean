import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Gradient.Sum

/-!
# Third-order H³ transport: gradient-majorant energy sum

The pointwise twelve-term gradient block is controlled by
`thirdOrderGradientMajorantDensity`.

This file introduces the corresponding square-energy majorant and performs
the finite coordinate bookkeeping.  The result is the exact identity

    ∑ j, ∑ i, ∑ k, ∑ l, Mgrad(i,k,l,j) = 24 E₃.

No integration theorem and no interpolation estimate is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderThreeGradientEnergy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
The square-energy counterpart of one velocity-axis gradient majorant.
-/
noncomputable def thirdOrderAxisGradientMajorantEnergy
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k l j r : PrimeTensor.Axis Depth.three) : ℝ :=
  4
      *
    spatialSquareEnergy
      (
        spatial3.d i
          (
            spatial3.d k
              (
                spatial3.d l
                  (loggedVelocityComponent u t j)
              )
          )
      )
    +
  spatialSquareEnergy
    (
      spatial3.d i
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t r)
            )
        )
    )
    +
  spatialSquareEnergy
    (
      spatial3.d i
        (
          spatial3.d k
            (
              spatial3.d r
                (loggedVelocityComponent u t j)
            )
        )
    )
    +
  spatialSquareEnergy
    (
      spatial3.d i
        (
          spatial3.d r
            (
              spatial3.d l
                (loggedVelocityComponent u t j)
            )
        )
    )
    +
  spatialSquareEnergy
    (
      spatial3.d r
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t j)
            )
        )
    )

/--
The full three-axis square-energy majorant for the twelve easy top-order
transport terms.
-/
noncomputable def thirdOrderGradientMajorantEnergy
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) : ℝ :=
  ∑ r : PrimeTensor.Axis Depth.three,
    thirdOrderAxisGradientMajorantEnergy
      u t i k l j r

/--
The complete four-index sum of the gradient majorant is exactly twenty-four
copies of the canonical third-order H³ energy.
-/
theorem sum_thirdOrderGradientMajorantEnergy_eq
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    (
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              thirdOrderGradientMajorantEnergy
                u t i k l j
    )
      =
    24 * velocityH3Energy3At u t := by

  classical

  unfold
    thirdOrderGradientMajorantEnergy
    thirdOrderAxisGradientMajorantEnergy
    velocityH3Energy3At

  simp only [axis_sum_three]

  ring

end Euclidean
end Bridge
end PrimeTensor
