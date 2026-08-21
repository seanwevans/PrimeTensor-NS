import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Direct.Closure

/-!
# Third-order H³ interpolation: L² membership bridge

`VelocityH3IntegrableAt` stores square-integrability as

    Integrable (fun x => f x ^ 2).

Mathlib's real `L²` characterization is

    MemLp f 2 volume ↔ Integrable (fun x => f x ^ 2),

but it requires `AEStronglyMeasurable f volume` as a separate hypothesis.

This file makes that distinction explicit.  It does not infer measurability from
square-integrability.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable local instance axisFintypeH3LandauL2Bridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3EnergyDerivative d

noncomputable local instance point3MeasureSpaceH3LandauL2Bridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3EnergyDerivative Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic square-integrability → L² bridge -/

theorem memLp_two_of_spatialL2SquareIntegrable
    {f : ScalarField3}
    (hMeas : AEStronglyMeasurable f volume)
    (hSq : SpatialL2SquareIntegrable f) :
    MeasureTheory.MemLp
      f
      (ENNReal.ofReal 2)
      volume := by

  have hTwo :
      MeasureTheory.MemLp
        f
        2
        volume :=
    (
      MeasureTheory.memLp_two_iff_integrable_sq
        hMeas
    ).2 hSq

  simpa using hTwo

/-! ## Extract the third-order square-integrability stored in H³ -/

theorem velocityH3IntegrableAt_third
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (j i k l : Axis Depth.three) :
    SpatialL2SquareIntegrable
      (
        spatial3.d i
          (
            spatial3.d k
              (
                spatial3.d l
                  (loggedVelocityComponent u t j)
              )
          )
      ) := by

  exact
    (hInt j).2.2.2 i k l

/--
A measurable third derivative in the H³ square-integrability class is an
`L²` function in the exact representation used by the Landau/Hölder layer.
-/
theorem velocityH3IntegrableAt_third_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (j i k l : Axis Depth.three)
    (
      hMeas :
        AEStronglyMeasurable
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
          volume
    ) :
    MeasureTheory.MemLp
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
      (ENNReal.ofReal 2)
      volume := by

  exact
    memLp_two_of_spatialL2SquareIntegrable
      hMeas
      (
        velocityH3IntegrableAt_third
          hInt j i k l
      )

end Euclidean
end Bridge
end PrimeTensor
