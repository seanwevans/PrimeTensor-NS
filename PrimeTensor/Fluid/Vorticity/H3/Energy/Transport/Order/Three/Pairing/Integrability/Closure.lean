import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Split
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Gradient.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Pairing.Integrability

/-!
# Order-three transport pairing: isolate the pure-transport obligation

The old `H3OrderThreeTransportPairingIntegrableAt` package contains:

1. integrability of the full third-order commutator pairing;
2. integrability of the pure transported-third-derivative pairing.

But the commutator has already been split exactly as

    C₃ = G₃ + I₃,

and both split pairings are now independently integrable:

* `H3OrderThreeGradientPairingIntegrableAt`;
* `H3OrderThreeInterpolationPairingIntegrableAt`.

Therefore the only genuinely separate whole-space assumption left in the old
package is the pure transported-third-derivative pairing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable local instance axisFintypeH3OrderThreePairingClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3OrderThreePairingClosure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3OrderThreePairingClosure Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The genuinely separate pure-transport half of the old order-three pairing
package.
-/
def H3OrderThreePureTransportPairingIntegrableAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀ i k l j : PrimeTensor.Axis Depth.three,
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
          thirdTransportedDerivative
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j x
      )
      volume

/--
Reconstruct the old full order-three pairing package from the two already
integrable split commutator blocks and the remaining pure-transport
integrability assumption.
-/
theorem h3OrderThreeTransportPairingIntegrableAt_of_pure
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
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
      hGradientPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    )
    (
      hInterpolationPairing :
        H3OrderThreeInterpolationPairingIntegrableAt
          u t
    )
    (
      hPure :
        H3OrderThreePureTransportPairingIntegrableAt
          u t
    ) :
    H3OrderThreeTransportPairingIntegrableAt
      u t := by

  rcases hClass.pressure_witness with
    ⟨p, s, hp4⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  intro i k l j

  constructor

  · change
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
        volume

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

    exact hGrad.add hInterp

  · change
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
            thirdTransportedDerivative
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j x
        )
        volume

    exact
      hPure i k l j

end Euclidean
end Bridge
end PrimeTensor
