import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.One.Integral
import PrimeTensor.Fluid.Vorticity.H3.Energy.Regularity

/-!
# Order-one transport pairing: isolate the genuine pure-transport obligation

`H3OrderOneTransportPairingIntegrableAt` contains two integrability statements:

1. the first commutator pairing;
2. the pure transported-derivative pairing.

The first is automatic from the H³ square-integrability data and the velocity
gradient envelope.  Only the second needs to remain as explicit whole-space
analytic input.

This file introduces the narrower pure-transport proposition and reconstructs
the older full pairing package from it.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable local instance axisFintypeH3OrderOnePairingClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
Only the pure transported first derivative needs to be assumed integrable.
The commutator half will be derived below.
-/
def H3OrderOnePureTransportPairingIntegrableAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀
    i j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            spatial3.d
                i
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component j
                )
                x
              *
            firstTransportedDerivative
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i j x
        )

private theorem firstDerivativeSquare_integrable_orderOnePairingClosure
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (c r : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          (
            spatial3.d
              r
              (loggedVelocityComponent u t c)
              x
          ) ^ 2
      ) := by

  have hC :=
    hH3 c

  dsimp only at hC

  simpa only [SpatialL2SquareIntegrable] using
    hC.2.1 r

private theorem firstPartial_spatialC1_orderOnePairingClosure
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
    (c r : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        spatial3.d
          r
          (loggedVelocityComponent u t c)
      ) := by

  change
    SpatialC1
      (
        spatial3.d
          r
          (
            fun y =>
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u t y
              ).component c
          )
      )

  exact
    s.velocity_firstPartial_spatialC1
      ht c r

private theorem firstTransportCommutator_spatialC1_orderOnePairingClosure
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
    (i j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        firstTransportCommutator
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t i j
      ) := by

  have hix :
      SpatialC1
        (
          spatial3.d
            i
            (loggedVelocityComponent u t xAxis)
        ) :=
    firstPartial_spatialC1_orderOnePairingClosure
      s ht xAxis i

  have hxj :
      SpatialC1
        (
          spatial3.d
            xAxis
            (loggedVelocityComponent u t j)
        ) :=
    firstPartial_spatialC1_orderOnePairingClosure
      s ht j xAxis

  have hiy :
      SpatialC1
        (
          spatial3.d
            i
            (loggedVelocityComponent u t yAxis)
        ) :=
    firstPartial_spatialC1_orderOnePairingClosure
      s ht yAxis i

  have hyj :
      SpatialC1
        (
          spatial3.d
            yAxis
            (loggedVelocityComponent u t j)
        ) :=
    firstPartial_spatialC1_orderOnePairingClosure
      s ht j yAxis

  have hiz :
      SpatialC1
        (
          spatial3.d
            i
            (loggedVelocityComponent u t zAxis)
        ) :=
    firstPartial_spatialC1_orderOnePairingClosure
      s ht zAxis i

  have hzj :
      SpatialC1
        (
          spatial3.d
            zAxis
            (loggedVelocityComponent u t j)
        ) :=
    firstPartial_spatialC1_orderOnePairingClosure
      s ht j zAxis

  unfold firstTransportCommutator

  exact
    (hix.mul hxj).add
      (
        (hiy.mul hyj).add
          (hiz.mul hzj)
      )

/--
The commutator half of the order-one pairing is integrable automatically.
-/
theorem h3OrderOneCommutatorPairingIntegrableAt_of_energyClass
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
    (i j : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          spatial3.d
              i
              (loggedVelocityComponent u t j)
              x
            *
          firstTransportCommutator
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i j x
      ) := by

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

  let prod : Point3 → ℝ :=
    fun x =>
      spatial3.d
          i
          (loggedVelocityComponent u t j)
          x
        *
      firstTransportCommutator
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t i j x

  let majorant : Point3 → ℝ :=
    fun x =>
      h t
        *
      (
        3
            *
          (
            spatial3.d
                i
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
          +
        (
          (
            spatial3.d
                xAxis
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
            +
          (
            (
              spatial3.d
                  yAxis
                  (loggedVelocityComponent u t j)
                  x
            ) ^ 2
              +
            (
              spatial3.d
                  zAxis
                  (loggedVelocityComponent u t j)
                  x
            ) ^ 2
          )
        )
      )

  have hF :
      SpatialC1
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        ) :=
    firstPartial_spatialC1_orderOnePairingClosure
      s htNS j i

  have hC :
      SpatialC1
        (
          firstTransportCommutator
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i j
        ) :=
    firstTransportCommutator_spatialC1_orderOnePairingClosure
      s htNS i j

  have hProdC1 :
      SpatialC1 prod := by
    unfold prod
    exact hF.mul hC

  have hProdMeas :
      MeasureTheory.AEStronglyMeasurable
        prod
        volume :=
    hProdC1.continuous.aestronglyMeasurable

  have hI :=
    firstDerivativeSquare_integrable_orderOnePairingClosure
      hH3 j i

  have hX :=
    firstDerivativeSquare_integrable_orderOnePairingClosure
      hH3 j xAxis

  have hY :=
    firstDerivativeSquare_integrable_orderOnePairingClosure
      hH3 j yAxis

  have hZ :=
    firstDerivativeSquare_integrable_orderOnePairingClosure
      hH3 j zAxis

  have hMajorant :
      MeasureTheory.Integrable
        majorant := by
    unfold majorant

    exact
      (
        (hI.const_mul 3).add
          (
            hX.add
              (
                hY.add hZ
              )
          )
      ).const_mul (h t)

  have hPointwise :
      ∀ x : Point3,
        ‖prod x‖ ≤ majorant x := by
    intro x

    have hDom :=
      firstTransportCommutator_density_le_gradientEnvelope
        hGradient
        i j x

    have hAbs :
        0 ≤ abs (prod x) :=
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
Reconstruct the old full order-one pairing package from the genuinely needed
pure-transport integrability assumption.
-/
theorem h3OrderOneTransportPairingIntegrableAt_of_pure
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
        H3OrderOnePureTransportPairingIntegrableAt
          u t
    ) :
    H3OrderOneTransportPairingIntegrableAt
      u t := by

  intro i j

  constructor

  · change
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            spatial3.d
                i
                (loggedVelocityComponent u t j)
                x
              *
            firstTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i j x
        )

    exact
      h3OrderOneCommutatorPairingIntegrableAt_of_energyClass
        hClass
        ht
        hH3
        hGradient
        i j

  · exact
      hPure i j

end Euclidean
end Bridge
end PrimeTensor
