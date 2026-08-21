import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Gradient.Integral
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Regularity.Closure

/-!
# Third-order gradient-pairing integrability from H³ control

The easy `D³u · Du` block does not need a separate integrability hypothesis.

For each fixed `(i,k,l,j)`, its energy pairing is pointwise dominated by

    h(t) * thirdOrderGradientMajorantDensity,

and that majorant is integrable using only the square-integrability of the
third derivatives already stored in `VelocityH3IntegrableAt`.

The H³ energy class supplies enough spatial regularity to make the pairing
continuous, hence strongly measurable.  Dominated integrability then closes the
argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable local instance axisFintypeH3GradientPairingClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

private theorem thirdDerivativeSquare_integrable_gradientPairingClosure
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
    (c r s q : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          (
            spatial3.d r
              (
                spatial3.d s
                  (
                    spatial3.d q
                      (loggedVelocityComponent u t c)
                  )
              )
              x
          ) ^ 2
      ) := by

  have hC :=
    hH3 c

  dsimp only at hC

  simpa only [SpatialL2SquareIntegrable] using
    hC.2.2.2 r s q

private theorem thirdOrderAxisGradientMajorantDensity_integrable_gradientPairingClosure
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
    (i k l j r : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          thirdOrderAxisGradientMajorantDensity
            u t i k l j r x
      ) := by

  have hF :=
    thirdDerivativeSquare_integrable_gradientPairingClosure
      hH3 j i k l

  have hB1 :=
    thirdDerivativeSquare_integrable_gradientPairingClosure
      hH3 r i k l

  have hB2 :=
    thirdDerivativeSquare_integrable_gradientPairingClosure
      hH3 j i k r

  have hB3 :=
    thirdDerivativeSquare_integrable_gradientPairingClosure
      hH3 j i r l

  have hB4 :=
    thirdDerivativeSquare_integrable_gradientPairingClosure
      hH3 j r k l

  unfold thirdOrderAxisGradientMajorantDensity

  exact
    (
      (
        (
          (hF.const_mul 4).add hB1
        ).add hB2
      ).add hB3
    ).add hB4

private theorem thirdOrderGradientMajorantDensity_integrable_gradientPairingClosure
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
    (i k l j : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          thirdOrderGradientMajorantDensity
            u t i k l j x
      ) := by

  have hX :=
    thirdOrderAxisGradientMajorantDensity_integrable_gradientPairingClosure
      hH3 i k l j xAxis

  have hY :=
    thirdOrderAxisGradientMajorantDensity_integrable_gradientPairingClosure
      hH3 i k l j yAxis

  have hZ :=
    thirdOrderAxisGradientMajorantDensity_integrable_gradientPairingClosure
      hH3 i k l j zAxis

  unfold thirdOrderGradientMajorantDensity

  exact
    hX.add
      (hY.add hZ)

private theorem thirdDerivative_spatialC1_gradientPairingClosure
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hRegular :
        H3OrderThreeTransportRegularityAt
          u t
    )
    (j i k l : PrimeTensor.Axis Depth.three) :
    SpatialC1
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

  have h2 :
      SpatialC2
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t j)
            )
        ) :=
    (hRegular k l j).2

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      h2 i

private theorem thirdTransportCommutatorAxisGradientBlock_spatialC1
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
      hRegular :
        H3OrderThreeTransportRegularityAt
          u t
    )
    (i k l j r : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        thirdTransportCommutatorAxisGradientBlock
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t i k l j r
      ) := by

  have hA1 :
      SpatialC1
        (
          spatial3.d i
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t r)
                )
            )
        ) :=
    thirdDerivative_spatialC1_gradientPairingClosure
      hRegular r i k l

  have hB1 :
      SpatialC1
        (
          spatial3.d r
            (loggedVelocityComponent u t j)
        ) := by
    change
      SpatialC1
        (
          spatial3.d r
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component j
            )
        )

    exact
      s.velocity_firstPartial_spatialC1
        ht j r

  have hA2 :
      SpatialC1
        (
          spatial3.d l
            (loggedVelocityComponent u t r)
        ) := by
    change
      SpatialC1
        (
          spatial3.d l
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component r
            )
        )

    exact
      s.velocity_firstPartial_spatialC1
        ht r l

  have hB2 :
      SpatialC1
        (
          spatial3.d i
            (
              spatial3.d k
                (
                  spatial3.d r
                    (loggedVelocityComponent u t j)
                )
            )
        ) :=
    thirdDerivative_spatialC1_gradientPairingClosure
      hRegular j i k r

  have hA3 :
      SpatialC1
        (
          spatial3.d k
            (loggedVelocityComponent u t r)
        ) := by
    change
      SpatialC1
        (
          spatial3.d k
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component r
            )
        )

    exact
      s.velocity_firstPartial_spatialC1
        ht r k

  have hB3 :
      SpatialC1
        (
          spatial3.d i
            (
              spatial3.d r
                (
                  spatial3.d l
                    (loggedVelocityComponent u t j)
                )
            )
        ) :=
    thirdDerivative_spatialC1_gradientPairingClosure
      hRegular j i r l

  have hA4 :
      SpatialC1
        (
          spatial3.d i
            (loggedVelocityComponent u t r)
        ) := by
    change
      SpatialC1
        (
          spatial3.d i
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component r
            )
        )

    exact
      s.velocity_firstPartial_spatialC1
        ht r i

  have hB4 :
      SpatialC1
        (
          spatial3.d r
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t j)
                )
            )
        ) :=
    thirdDerivative_spatialC1_gradientPairingClosure
      hRegular j r k l

  unfold thirdTransportCommutatorAxisGradientBlock

  exact
    (
      (
        (hA1.mul hB1).add
          (hA2.mul hB2)
      ).add
        (hA3.mul hB3)
    ).add
      (hA4.mul hB4)

private theorem thirdTransportCommutatorGradientBlock_spatialC1
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
      hRegular :
        H3OrderThreeTransportRegularityAt
          u t
    )
    (i k l j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        thirdTransportCommutatorGradientBlock
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t i k l j
      ) := by

  have hX :=
    thirdTransportCommutatorAxisGradientBlock_spatialC1
      s ht hRegular i k l j xAxis

  have hY :=
    thirdTransportCommutatorAxisGradientBlock_spatialC1
      s ht hRegular i k l j yAxis

  have hZ :=
    thirdTransportCommutatorAxisGradientBlock_spatialC1
      s ht hRegular i k l j zAxis

  unfold thirdTransportCommutatorGradientBlock

  exact
    hX.add
      (hY.add hZ)

/--
The split third-order gradient pairing is automatically integrable from the
energy class, H³ square-integrability, and the velocity-gradient envelope.
-/
theorem h3OrderThreeGradientPairingIntegrableAt_of_energyClass
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
    ) :
    H3OrderThreeGradientPairingIntegrableAt
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

  have hRegular :
      H3OrderThreeTransportRegularityAt
        u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass
      hClass
      ht

  intro i k l j

  let prod : Point3 → ℝ :=
    fun x =>
      spatial3.d i
          (
            spatial3.d k
              (
                spatial3.d l
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

  let majorant : Point3 → ℝ :=
    fun x =>
      h t
        *
      thirdOrderGradientMajorantDensity
        u t i k l j x

  have hF :
      SpatialC1
        (
          spatial3.d i
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t j)
                )
            )
        ) :=
    thirdDerivative_spatialC1_gradientPairingClosure
      hRegular j i k l

  have hG :
      SpatialC1
        (
          thirdTransportCommutatorGradientBlock
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j
        ) :=
    thirdTransportCommutatorGradientBlock_spatialC1
      s htNS hRegular i k l j

  have hProdC1 :
      SpatialC1 prod := by
    unfold prod
    exact hF.mul hG

  have hProdMeas :
      MeasureTheory.AEStronglyMeasurable
        prod
        volume :=
    hProdC1.continuous.aestronglyMeasurable

  have hDensity :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            thirdOrderGradientMajorantDensity
              u t i k l j x
        ) :=
    thirdOrderGradientMajorantDensity_integrable_gradientPairingClosure
      hH3 i k l j

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
      thirdTransportCommutatorGradientBlock_density_le_gradientEnvelope
        hGradient
        i k l j x

    have hAbs :
        0 ≤
          abs
            (
              spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
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

end Euclidean
end Bridge
end PrimeTensor
