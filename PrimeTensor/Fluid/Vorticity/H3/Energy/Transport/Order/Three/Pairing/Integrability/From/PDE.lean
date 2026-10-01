import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Pairing.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.PDE.Split

/-!
# Recover top-order transport pairing integrability from the PDE package

At order three the canonical PDE splitting package already stores integrability
of the full transport pairing

    D³u · D³((u · ∇)u).

The exact transport decomposition writes this as

    D³u · C₃ + D³u · (u · ∇D³u).

The gradient and interpolation closures independently give integrability of the
commutator pairing `D³u · C₃`. Subtracting that integrable commutator product
from the integrable full transport product gives integrability of the pure
transport product.

The theorem constructs `H3OrderThreeTransportPairingIntegrableAt` directly,
avoiding the older pure-transport wrapper and its unrelated local measure-space
instance.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3OrderThreeFromPDE
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical PDE pairing integrability plus the already-closed commutator
integrability gives the complete top-order transport pairing package. -/
theorem h3OrderThreeTransportPairingIntegrableAt_of_pde
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
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hPDE :
        H3PDEPairingIntegrableAt
          u p t
    )
    (
      hGradientPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    )
    (
      hInterpolationPairing :
        H3OrderThreeInterpolationPairingIntegrableAt
          u t
    ) :
    H3OrderThreeTransportPairingIntegrableAt
      u t := by

  rcases hClass.pressure_witness with
    ⟨p₀, s, hp4⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  have hRegular :
      H3OrderThreeTransportRegularityAt
        u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass
      hClass
      ht

  unfold H3PDEPairingIntegrableAt at hPDE
  dsimp only at hPDE

  intro i k l j

  have hComm :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            thirdTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j x
        )
        volume := by

    have hGrad :=
      hGradientPairing i k l j

    have hInterp :=
      hInterpolationPairing i k l j

    have hEq :
        (
          fun x : Point3 =>
            spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            thirdTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j x
        )
          =
        (
          fun x : Point3 =>
            spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            thirdTransportCommutatorGradientBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j x
              +
            spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            thirdTransportCommutatorInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j x
        ) := by

      funext x

      rw [
        thirdTransportCommutator_eq_gradient_add_interpolation
          s htNS x i k l j
      ]

      ring

    rw [hEq]

    exact
      hGrad.add hInterp

  constructor

  · exact hComm

  · have hFull :
        MeasureTheory.Integrable
          (
            fun x : Point3 =>
              spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (
                        spatial3.d
                          l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              momentumTransport3Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j x
          )
          volume := by
      exact
        (hPDE.2.2.2 i k l j).2.1

    have hDifference :
        MeasureTheory.Integrable
          (
            fun x : Point3 =>
              spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (
                        spatial3.d
                          l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              momentumTransport3Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j x
                -
              spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (
                        spatial3.d
                          l
                          (loggedVelocityComponent u t j)
                      )
                  )
                  x
                *
              thirdTransportCommutator
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j x
          )
          volume :=
      hFull.sub hComm

    have hPointwise :
        (
          fun x : Point3 =>
            spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            momentumTransport3Component
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j x
              -
            spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            thirdTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j x
        )
          =
        (
          fun x : Point3 =>
            spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            thirdTransportedDerivative
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j x
        ) := by

      funext x

      have hSplit :=
        congrFun
          (
            momentumTransport3Component_eq_commutator_add_transport
              s
              htNS
              hRegular
              i k l j
          )
          x

      rw [hSplit]

      ring

    rw [hPointwise] at hDifference

    exact hDifference

end

end Euclidean
end Bridge
end PrimeTensor
