import PrimeTensor.Fluid.Vorticity.H3.Energy.PDE.Split

/-!
# Spatial linearity for the higher-order H³ momentum split

`VorticityH3EnergyPDESplit` isolated one purely local bookkeeping hypothesis:

    HigherOrderMomentumRHSSplitsAt v p t

saying that the second- and third-order spatial derivatives of the momentum
right-hand side distribute over

    diffusion - transport - pressure.

This file discharges that equality hypothesis from the exact regularity needed
by the project's existing derivative-linearity theorem

    SpatialC1.spatial3_d_sub.

No integration, PDE estimate, or harmonic analysis occurs here.

For order two we need the order-one diffusion, transport, and pressure fields
to be `SpatialC1`.  For order three we additionally need their order-two
derivatives to be `SpatialC1`.

The endpoint corollaries replace `HigherOrderMomentumRHSSplitsAt` by this
regularity package in the canonical H³ energy decomposition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
Regularity needed solely to distribute the next spatial derivative through
the order-one and order-two momentum decompositions.
-/
def HigherOrderMomentumSplitRegularityAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : Prop :=
  (
    ∀
      k j : PrimeTensor.Axis Depth.three,
        SpatialC1
            (momentumDiffusion1Component v t k j)
          ∧
        SpatialC1
            (momentumTransport1Component v t k j)
          ∧
        SpatialC1
            (
              fun x =>
                momentumDiffusion1Component v t k j x
                  -
                momentumTransport1Component v t k j x
            )
          ∧
        SpatialC1
            (momentumPressure1Component p t k j)
  )
    ∧
  (
    ∀
      k l j : PrimeTensor.Axis Depth.three,
        SpatialC1
            (momentumDiffusion2Component v t k l j)
          ∧
        SpatialC1
            (momentumTransport2Component v t k l j)
          ∧
        SpatialC1
            (
              fun x =>
                momentumDiffusion2Component v t k l j x
                  -
                momentumTransport2Component v t k l j x
            )
          ∧
        SpatialC1
            (momentumPressure2Component p t k l j)
  )

/--
Order-two momentum splitting follows from `SpatialC1.spatial3_d_sub`.
-/
theorem momentumRHS2Component_eq_split_of_spatialC1
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      hRegular :
        HigherOrderMomentumSplitRegularityAt
          v p t
    )
    (i k j : PrimeTensor.Axis Depth.three) :
    momentumRHS2Component
        v p t i k j
      =
    fun x =>
      momentumDiffusion2Component
          v t i k j x
        -
      momentumTransport2Component
          v t i k j x
        -
      momentumPressure2Component
          p t i k j x := by

  rcases hRegular.1 k j with
    ⟨
      hDiffusion,
      hTransport,
      hDiffusionTransport,
      hPressure
    ⟩

  funext x

  unfold momentumRHS2Component

  rw [
    momentumRHS1Component_eq_split
  ]

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hDiffusionTransport hPressure x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hDiffusion hTransport x i
  ]

  rfl

/--
Order-three momentum splitting follows by differentiating the already split
order-two field once more.
-/
theorem momentumRHS3Component_eq_split_of_spatialC1
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      hRegular :
        HigherOrderMomentumSplitRegularityAt
          v p t
    )
    (i k l j : PrimeTensor.Axis Depth.three) :
    momentumRHS3Component
        v p t i k l j
      =
    fun x =>
      momentumDiffusion3Component
          v t i k l j x
        -
      momentumTransport3Component
          v t i k l j x
        -
      momentumPressure3Component
          p t i k l j x := by

  rcases hRegular.2 k l j with
    ⟨
      hDiffusion,
      hTransport,
      hDiffusionTransport,
      hPressure
    ⟩

  have hSplit2 :
      momentumRHS2Component
          v p t k l j
        =
      fun x =>
        momentumDiffusion2Component
            v t k l j x
          -
        momentumTransport2Component
            v t k l j x
          -
        momentumPressure2Component
            p t k l j x :=
    momentumRHS2Component_eq_split_of_spatialC1
      hRegular k l j

  funext x

  unfold momentumRHS3Component

  change
    spatial3.d
        i
        (momentumRHS2Component v p t k l j)
        x
      =
    momentumDiffusion3Component
        v t i k l j x
      -
    momentumTransport3Component
        v t i k l j x
      -
    momentumPressure3Component
        p t i k l j x

  rw [hSplit2]

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hDiffusionTransport hPressure x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hDiffusion hTransport x i
  ]

  rfl

/--
The abstract higher-order split package is a theorem of the local spatial
regularity package above.
-/
theorem higherOrderMomentumRHSSplitsAt_of_spatialC1
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      hRegular :
        HigherOrderMomentumSplitRegularityAt
          v p t
    ) :
    HigherOrderMomentumRHSSplitsAt
      v p t := by

  constructor

  · intro i k j

    exact
      momentumRHS2Component_eq_split_of_spatialC1
        hRegular i k j

  · intro i k l j

    exact
      momentumRHS3Component_eq_split_of_spatialC1
        hRegular i k l j

/--
Full canonical PDE derivative split with the higher-order equality assumption
replaced by explicit local `SpatialC1` regularity.
-/
theorem velocityH3PDEDerivativeAt_eq_split_of_spatialC1
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      hRegular :
        HigherOrderMomentumSplitRegularityAt
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p t
    )
    (
      hInt :
        H3PDEPairingIntegrableAt
          u p t
    ) :
    velocityH3PDEDerivativeAt u p t
      =
    velocityH3DiffusionDerivativeAt u t
      -
    velocityH3TransportDerivativeAt u t
      -
    velocityH3PressureDerivativeAt u p t := by

  exact
    velocityH3PDEDerivativeAt_eq_split
      (
        higherOrderMomentumRHSSplitsAt_of_spatialC1
          hRegular
      )
      hInt

/--
Canonical H³ derivative decomposition with no free higher-order field-equality
hypothesis.
-/
theorem deriv_velocityH3EnergyAt_eq_diffusion_sub_transport_sub_pressure_of_spatialC1
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      hDerivative :
        H3OrderEnergyDerivativeIdentities
          u t
    )
    (
      hRegular :
        HigherOrderMomentumSplitRegularityAt
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p t
    )
    (
      hInt :
        H3PDEPairingIntegrableAt
          u p t
    ) :
    deriv
        (velocityH3EnergyAt u)
        t
      =
    velocityH3DiffusionDerivativeAt u t
      -
    velocityH3TransportDerivativeAt u t
      -
    velocityH3PressureDerivativeAt u p t := by

  exact
    deriv_velocityH3EnergyAt_eq_diffusion_sub_transport_sub_pressure
      s
      ht
      hDerivative
      (
        higherOrderMomentumRHSSplitsAt_of_spatialC1
          hRegular
      )
      hInt

end Euclidean
end Bridge
end PrimeTensor
