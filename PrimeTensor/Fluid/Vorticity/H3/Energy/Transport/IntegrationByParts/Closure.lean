import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Cancellation
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.One.Pairing.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Two.Pairing.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Pairing.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Regularity.Closure

/-!
# Honest whole-space transport integration by parts

The older transport-tail interface carried, at each differentiated order,

* a flux-divergence integral equal to zero; and
* a separate pure-transport pairing integrability hypothesis.

That split is an artifact of Mathlib's total integral: writing

    ∫ div (u f²) = 0

does not by itself assert that the divergence is integrable.

At order zero the older interface had the same total-integral issue but no
separate pairing-integrability field.  We therefore strengthen that field to
the same honest IBP form as well.

The mathematically natural datum is therefore

    Integrable (div (u f²)) ∧ ∫ div (u f²) = 0.

For an incompressible preterminal solution the already-proved pointwise identity

    div (u f²) = 2 f (u · ∇f)

shows that this single datum also supplies the pure-transport pairing
integrability.  Thus the new interface is equivalent to the old
`flux + pure pairing` pair, while making the whole-space analytic content
explicit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable local instance axisFintypeH3TransportIBPClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TransportIBPClosure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3TransportIBPClosure Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-!
## Order zero
-/

/--
Proper whole-space integration-by-parts datum for the componentwise kinetic
energy flux.  Unlike `TransportEnergyFluxVanishesAt`, this explicitly records
integrability of every flux divergence before asserting that its integral
vanishes.
-/
def TransportEnergyIntegrationByPartsAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            transportEnergyFluxDivergenceXYZ
              v t j x
        )
        volume
  )
    ∧
  TransportEnergyFluxVanishesAt
    v t

/--
An honest order-zero IBP datum makes the transport-energy pairing integrable.
This is the analytic fact missing from the older total-integral-only flux
predicate.
-/
theorem transportEnergyPairingIntegrable_of_integrationByParts
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          v p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      hIBP :
        TransportEnergyIntegrationByPartsAt
          v t
    )
    (j : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          (v t x).component j
            *
          realAdvectionComponent
            v t x j
      )
      volume := by

  have hPointwise :
      (
        fun x : Point3 =>
          transportEnergyFluxDivergenceXYZ
            v t j x
      )
        =
      (
        fun x : Point3 =>
          2
            *
          (
            (v t x).component j
              *
            realAdvectionComponent
              v t x j
          )
      ) := by

    funext x

    simpa [mul_assoc] using
      transportEnergyFluxDivergenceXYZ_eq_two_mul_advection
        s ht j x

  have hTwice :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            2
              *
            (
              (v t x).component j
                *
              realAdvectionComponent
                v t x j
            )
        )
        volume := by

    rw [← hPointwise]

    exact hIBP.1 j

  have hHalf :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            (1 / 2 : ℝ)
              *
            (
              2
                *
              (
                (v t x).component j
                  *
                realAdvectionComponent
                  v t x j
              )
            )
        )
        volume :=
    hTwice.const_mul (1 / 2 : ℝ)

  have hEq :
      (
        fun x : Point3 =>
          (1 / 2 : ℝ)
            *
          (
            2
              *
            (
              (v t x).component j
                *
              realAdvectionComponent
                v t x j
            )
          )
      )
        =
      (
        fun x : Point3 =>
          (v t x).component j
            *
          realAdvectionComponent
            v t x j
      ) := by

    funext x
    ring

  rw [hEq] at hHalf

  exact hHalf

/--
Logged order-zero whole-space IBP data.
-/
def H3TransportEnergyIntegrationByPartsAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  TransportEnergyIntegrationByPartsAt
    (
      PrimeTensor.Bridge.logSpaceTimeVectorField
        u
    )
    t

/--
Forget the explicit integrability field and recover the older order-zero flux
predicate expected by the existing cancellation theorem.
-/
theorem h3TransportEnergyFluxVanishesAt_of_integrationByParts
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3TransportEnergyIntegrationByPartsAt
          u t
    ) :
    H3TransportEnergyFluxVanishesAt
      u t := by

  exact hIBP.2

/-!
## Differentiated scalar transport
-/

/--
Proper whole-space integration-by-parts datum for one transported scalar field.
-/
def TransportScalarIntegrationByPartsAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (f : ScalarField3) : Prop :=
  MeasureTheory.Integrable
      (
        fun x : Point3 =>
          transportScalarFluxDivergenceXYZ
            v t f x
      )
      volume
    ∧
  TransportScalarFluxVanishesAt
    v t f

/--
The old `flux + pure pairing integrable` data imply the honest IBP datum.
-/
theorem transportScalarIntegrationByPartsAt_of_flux_of_pairing
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
    {T t : ℝ}
    {f : ScalarField3}
    (
      s :
        PreterminalNavierStokes3
          v p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      hf :
        SpatialC1 f
    )
    (
      hFlux :
        TransportScalarFluxVanishesAt
          v t f
    )
    (
      hPairing :
        MeasureTheory.Integrable
          (
            fun x : Point3 =>
              f x
                *
              h3ScalarTransport
                v t f x
          )
          volume
    ) :
    TransportScalarIntegrationByPartsAt
      v t f := by

  constructor

  · have hPointwise :
        (
          fun x : Point3 =>
            transportScalarFluxDivergenceXYZ
              v t f x
        )
          =
        (
          fun x : Point3 =>
            2
              *
            (
              f x
                *
              h3ScalarTransport
                v t f x
            )
        ) := by

      funext x

      simpa [mul_assoc] using
        transportScalarFluxDivergenceXYZ_eq_two_mul_transport
          s ht hf x

    rw [hPointwise]

    exact
      hPairing.const_mul 2

  · exact hFlux

/--
The honest IBP datum automatically gives the pure transported-scalar pairing
integrability.
-/
theorem transportScalarPairingIntegrable_of_integrationByParts
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
    {T t : ℝ}
    {f : ScalarField3}
    (
      s :
        PreterminalNavierStokes3
          v p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      hf :
        SpatialC1 f
    )
    (
      hIBP :
        TransportScalarIntegrationByPartsAt
          v t f
    ) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          f x
            *
          h3ScalarTransport
            v t f x
      )
      volume := by

  have hPointwise :
      (
        fun x : Point3 =>
          transportScalarFluxDivergenceXYZ
            v t f x
      )
        =
      (
        fun x : Point3 =>
          2
            *
          (
            f x
              *
            h3ScalarTransport
              v t f x
          )
      ) := by

    funext x

    simpa [mul_assoc] using
      transportScalarFluxDivergenceXYZ_eq_two_mul_transport
        s ht hf x

  have hTwice :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            2
              *
            (
              f x
                *
              h3ScalarTransport
                v t f x
            )
        )
        volume := by

    rw [← hPointwise]

    exact hIBP.1

  have hHalf :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            (1 / 2 : ℝ)
              *
            (
              2
                *
              (
                f x
                  *
                h3ScalarTransport
                  v t f x
              )
            )
        )
        volume :=
    hTwice.const_mul (1 / 2 : ℝ)

  have hEq :
      (
        fun x : Point3 =>
          (1 / 2 : ℝ)
            *
          (
            2
              *
            (
              f x
                *
              h3ScalarTransport
                v t f x
            )
          )
      )
        =
      (
        fun x : Point3 =>
          f x
            *
          h3ScalarTransport
            v t f x
      ) := by

    funext x
    ring

  rw [hEq] at hHalf

  exact hHalf

/-! ## Logged H³ order wrappers -/

/--
Honest whole-space IBP data for every first velocity derivative.
-/
def H3FirstDerivativeTransportIntegrationByPartsAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀ i j : PrimeTensor.Axis Depth.three,
    TransportScalarIntegrationByPartsAt
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t
      (
        spatial3.d
          i
          (loggedVelocityComponent u t j)
      )

/--
Honest whole-space IBP data for every second velocity derivative.
-/
def H3SecondDerivativeTransportIntegrationByPartsAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀ i k j : PrimeTensor.Axis Depth.three,
    TransportScalarIntegrationByPartsAt
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t
      (
        spatial3.d
          i
          (
            spatial3.d
              k
              (loggedVelocityComponent u t j)
          )
      )

/--
Honest whole-space IBP data for every third velocity derivative.
-/
def H3ThirdDerivativeTransportIntegrationByPartsAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀ i k l j : PrimeTensor.Axis Depth.three,
    TransportScalarIntegrationByPartsAt
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t
      (
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
      )

/-! ## Recover the old flux predicates -/

theorem h3FirstDerivativeTransportFluxVanishesAt_of_integrationByParts
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3FirstDerivativeTransportIntegrationByPartsAt
          u t
    ) :
    H3FirstDerivativeTransportFluxVanishesAt
      u t := by

  intro i j

  change
    TransportScalarFluxVanishesAt
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t
      (
        spatial3.d
          i
          (loggedVelocityComponent u t j)
      )

  exact
    (hIBP i j).2

theorem h3SecondDerivativeTransportFluxVanishesAt_of_integrationByParts
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3SecondDerivativeTransportIntegrationByPartsAt
          u t
    ) :
    H3SecondDerivativeTransportFluxVanishesAt
      u t := by

  intro i k j

  change
    TransportScalarFluxVanishesAt
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t
      (
        spatial3.d
          i
          (
            spatial3.d
              k
              (loggedVelocityComponent u t j)
          )
      )

  exact
    (hIBP i k j).2

theorem h3ThirdDerivativeTransportFluxVanishesAt_of_integrationByParts
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hIBP :
        H3ThirdDerivativeTransportIntegrationByPartsAt
          u t
    ) :
    H3ThirdDerivativeTransportFluxVanishesAt
      u t := by

  intro i k l j

  change
    TransportScalarFluxVanishesAt
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t
      (
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
      )

  exact
    (hIBP i k l j).2

/-! ## Recover the old pure-pairing integrability predicates -/

theorem h3OrderOnePureTransportPairingIntegrableAt_of_integrationByParts
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
      hIBP :
        H3FirstDerivativeTransportIntegrationByPartsAt
          u t
    ) :
    H3OrderOnePureTransportPairingIntegrableAt
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

  intro i j

  have hf :
      SpatialC1
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        ) := by

    change
      SpatialC1
        (
          spatial3.d
            i
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
        htNS j i

  have hProd :=
    transportScalarPairingIntegrable_of_integrationByParts
      s
      htNS
      hf
      (hIBP i j)

  change
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          spatial3.d
              i
              (loggedVelocityComponent u t j)
              x
            *
          firstTransportedDerivative
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i j x
      )
      volume

  unfold firstTransportedDerivative

  exact hProd

theorem h3OrderTwoPureTransportPairingIntegrableAt_of_integrationByParts
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
      hIBP :
        H3SecondDerivativeTransportIntegrationByPartsAt
          u t
    ) :
    H3OrderTwoPureTransportPairingIntegrableAt
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

  intro i k j

  have hSecond2 :
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

  have hf :
      SpatialC1
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (loggedVelocityComponent u t j)
            )
        ) := by

    unfold SpatialC2 at hSecond2
    unfold SpatialC1

    exact
      hSecond2.of_le
        (by norm_num)

  have hProd :=
    transportScalarPairingIntegrable_of_integrationByParts
      s
      htNS
      hf
      (hIBP i k j)

  change
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
          secondTransportedDerivative
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k j x
      )
      volume

  unfold secondTransportedDerivative

  exact hProd

theorem h3OrderThreePureTransportPairingIntegrableAt_of_integrationByParts
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
      hIBP :
        H3ThirdDerivativeTransportIntegrationByPartsAt
          u t
    ) :
    H3OrderThreePureTransportPairingIntegrableAt
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

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨
      le_of_lt ht.1,
      ht.2
    ⟩

  intro i k l j

  have hSecond3 :
      SpatialC3
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (loggedVelocityComponent u t j)
            )
        ) := by

    change
      SpatialC3
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (
                  fun x =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t x
                    ).component j
                )
            )
        )

    exact
      hClass.velocity_spatial_five
        t htTail j k l

  have hThird2 :
      SpatialC2
        (
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
        ) := by

    change
      SpatialC2
        (
          fun q =>
            partialDeriv
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
              q
        )

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
        hSecond3 i

  have hf :
      SpatialC1
        (
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
        ) := by

    unfold SpatialC2 at hThird2
    unfold SpatialC1

    exact
      hThird2.of_le
        (by norm_num)

  have hProd :=
    transportScalarPairingIntegrable_of_integrationByParts
      s
      htNS
      hf
      (hIBP i k l j)

  change
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

  unfold thirdTransportedDerivative

  exact hProd

end Euclidean
end Bridge
end PrimeTensor
