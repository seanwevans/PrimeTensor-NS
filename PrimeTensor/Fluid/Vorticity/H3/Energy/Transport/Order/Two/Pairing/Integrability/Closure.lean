import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Two.Integral
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Regularity.Closure

/-!
# Order-two transport pairing: isolate the pure-transport obligation

`H3OrderTwoTransportPairingIntegrableAt` contains two integrability statements:

1. the second-order commutator pairing;
2. the pure transported-second-derivative pairing.

The first is automatic from:

* `VelocityH3IntegrableAt`, which integrates the quadratic majorant;
* `VelocityGradientEnvelope`, which supplies the pointwise bound;
* `PreterminalH3EnergyClass`, which supplies the regularity needed for
  measurability.

Only the pure transport half remains as explicit whole-space analytic input.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable local instance axisFintypeH3OrderTwoPairingClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
Only the pure transported second derivative needs to be assumed integrable.
The commutator half is reconstructed below.
-/
def H3OrderTwoPureTransportPairingIntegrableAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀
    i k j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      fun y =>
                        (
                          PrimeTensor.Bridge.logSpaceTimeVectorField
                            u t y
                        ).component j
                    )
                )
                x
              *
            secondTransportedDerivative
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k j x
        )

/--
The commutator half of the order-two transport pairing is automatic from the
H³ energy class, H³ square-integrability, and the gradient envelope.
-/
theorem h3OrderTwoCommutatorPairingIntegrableAt_of_energyClass
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    {h : ℝ → ℝ}
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
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    )
    (i k j : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
              x
            *
          secondTransportCommutator
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k j x
      ) := by

  let prod : Point3 → ℝ :=
    fun x =>
      spatial3.d
          i
          (
            spatial3.d
              k
              (loggedVelocityComponent u t j)
          )
          x
        *
      secondTransportCommutator
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t i k j x

  let majorant : Point3 → ℝ :=
    fun x =>
      h t
        *
      secondOrderCommutatorMajorantDensity
        u t i k j x

  have hRegular :
      H3OrderThreeTransportRegularityAt
        u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass
      hClass
      ht

  have hOuter2 :
      SpatialC2
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (loggedVelocityComponent u t j)
            )
        ) :=
    (hRegular i k j).2

  have hComm1 :
      SpatialC1
        (
          secondTransportCommutator
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k j
        ) :=
    (hRegular i k j).1

  have hOuterContinuous :
      Continuous
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (loggedVelocityComponent u t j)
            )
        ) := by
    unfold SpatialC2 at hOuter2
    exact hOuter2.continuous

  have hCommContinuous :
      Continuous
        (
          secondTransportCommutator
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k j
        ) := by
    unfold SpatialC1 at hComm1
    exact hComm1.continuous

  have hProdMeas :
      MeasureTheory.AEStronglyMeasurable
        prod
        volume := by
    unfold prod
    exact
      (hOuterContinuous.mul hCommContinuous).aestronglyMeasurable

  have hDensity :
      MeasureTheory.Integrable
        (
          secondOrderCommutatorMajorantDensity
            u t i k j
        ) :=
    secondOrderCommutatorMajorantDensity_integrable
      hH3 i k j

  have hMajorant :
      MeasureTheory.Integrable
        majorant := by
    unfold majorant
    exact hDensity.const_mul (h t)

  have hPointwise :
      ∀ x : Point3,
        ‖prod x‖ ≤ majorant x := by
    intro x

    have hDom :=
      secondTransportCommutator_density_le_gradientEnvelope
        hClass
        ht
        hGradient
        i k j x

    have hAbs :
        0 ≤
          abs
            (
              spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
                *
              secondTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k j x
            ) :=
      abs_nonneg _

    unfold prod majorant

    rw [Real.norm_eq_abs]

    linarith

  exact
    hMajorant.mono'
      hProdMeas
      (
        Filter.Eventually.of_forall
          hPointwise
      )

/--
Reconstruct the old full order-two pairing package from the genuinely needed
pure-transport integrability assumption.
-/
theorem h3OrderTwoTransportPairingIntegrableAt_of_pure
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    {h : ℝ → ℝ}
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
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    )
    (
      hPure :
        H3OrderTwoPureTransportPairingIntegrableAt
          u t
    ) :
    H3OrderTwoTransportPairingIntegrableAt
      u t := by

  intro i k j

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
                    (loggedVelocityComponent u t j)
                )
                x
              *
            secondTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k j x
        )

    exact
      h3OrderTwoCommutatorPairingIntegrableAt_of_energyClass
        hClass
        ht
        hH3
        hGradient
        i k j

  · exact
      hPure i k j

end Euclidean
end Bridge
end PrimeTensor
