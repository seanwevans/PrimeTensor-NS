import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderTwo

/-!
# Third-order transport commutator decomposition

This is the top transport level of the canonical H³ energy.

The green order-two decomposition has the form

    ∂ₖ∂ₗ ((v · ∇)vⱼ)
      =
    C₂(k,l,j)
      +
    v · ∇(∂ₖ∂ₗvⱼ).

Differentiate once more in direction `i`.  The derivative of the pure
transport term again splits as

    ∂ᵢ (v · ∇f)
      =
    (∂ᵢv · ∇)f
      +
    v · ∇(∂ᵢf).

Hence the third-order transport term is

    third commutator
      +
    pure transport of ∂ᵢ∂ₖ∂ₗvⱼ.

The pure transport piece cancels under the same explicit whole-space scalar
flux condition used at lower orders.  This file deliberately keeps the
regularity needed to differentiate the order-two decomposition as an explicit
package; no L² commutator estimate is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderThree
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-! ## Small regularity helper -/

private theorem firstPartial_spatialC1_of_spatialC2_orderThree
    {f : ScalarField3}
    (
      hf :
        SpatialC2 f
    )
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        spatial3.d i f
      ) := by

  change
    SpatialC1
      (
        fun y =>
          partialDeriv i f y
      )

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hf i


private theorem h3ScalarTransport_spatialC1_orderThree
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
    {f : ScalarField3}
    (
      hf :
        SpatialC2 f
    ) :
    SpatialC1
      (
        h3ScalarTransport
          v t f
      ) := by

  have hux :=
    s.velocity_component_spatialC1
      ht xAxis

  have huy :=
    s.velocity_component_spatialC1
      ht yAxis

  have huz :=
    s.velocity_component_spatialC1
      ht zAxis

  have hfx :
      SpatialC1
        (
          spatial3.d xAxis f
        ) :=
    firstPartial_spatialC1_of_spatialC2_orderThree
      hf xAxis

  have hfy :
      SpatialC1
        (
          spatial3.d yAxis f
        ) :=
    firstPartial_spatialC1_of_spatialC2_orderThree
      hf yAxis

  have hfz :
      SpatialC1
        (
          spatial3.d zAxis f
        ) :=
    firstPartial_spatialC1_of_spatialC2_orderThree
      hf zAxis

  unfold h3ScalarTransport

  exact
    (hux.mul hfx).add
      (
        (huy.mul hfy).add
          (huz.mul hfz)
      )

/-! ## Top-order regularity package -/

/--
Regularity needed only to differentiate the already-proved order-two
decomposition.

The first conjunct says the order-two commutator is `C¹`.
The second says every second velocity partial used as the transported scalar is
`C²`, which is exactly what `spatial_d_h3ScalarTransport` requires.
-/
def ThirdOrderTransportRegularityAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : Prop :=
  ∀
    k l j : PrimeTensor.Axis Depth.three,
      SpatialC1
          (
            secondTransportCommutator
              v t k l j
          )
        ∧
      SpatialC2
          (
            spatial3.d
              k
              (
                spatial3.d
                  l
                  (
                    fun x =>
                      (v t x).component j
                  )
              )
          )

/-! ## Exact third-order split -/

/--
All non-pure-transport terms generated at spatial derivative order three.
-/
noncomputable def thirdTransportCommutator
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    spatial3.d
        i
        (
          secondTransportCommutator
            v t k l j
        )
        x
      +
    scalarTransportDerivativeCommutator
        v t i
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (
                  fun q =>
                    (v t q).component j
                )
            )
        )
        x

/--
The pure transported third derivative.
-/
noncomputable def thirdTransportedDerivative
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  h3ScalarTransport
    v t
    (
      spatial3.d
        i
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (
                  fun q =>
                    (v t q).component j
                )
            )
        )
    )

/--
Exact order-three transport decomposition.
-/
theorem momentumTransport3Component_eq_commutator_add_transport
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
      hRegular :
        ThirdOrderTransportRegularityAt
          v t
    )
    (i k l j : PrimeTensor.Axis Depth.three) :
    momentumTransport3Component
        v t i k l j
      =
    fun x =>
      thirdTransportCommutator
          v t i k l j x
        +
      thirdTransportedDerivative
          v t i k l j x := by

  have hComm :
      SpatialC1
        (
          secondTransportCommutator
            v t k l j
        ) :=
    (hRegular k l j).1

  have hF2 :
      SpatialC2
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (
                  fun x =>
                    (v t x).component j
                )
            )
        ) :=
    (hRegular k l j).2

  have hPure :
      SpatialC1
        (
          secondTransportedDerivative
            v t k l j
        ) := by

    unfold secondTransportedDerivative

    exact
      h3ScalarTransport_spatialC1_orderThree
        s ht hF2

  funext x

  unfold momentumTransport3Component

  change
    spatial3.d
        i
        (
          momentumTransport2Component
            v t k l j
        )
        x
      =
    thirdTransportCommutator
        v t i k l j x
      +
    thirdTransportedDerivative
        v t i k l j x

  rw [
    momentumTransport2Component_eq_commutator_add_transport
      s ht k l j
  ]

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hComm hPure x i
  ]

  unfold secondTransportedDerivative

  rw [
    spatial_d_h3ScalarTransport
      s ht hF2 x i
  ]

  unfold
    thirdTransportCommutator
    thirdTransportedDerivative

  ring

/-! ## Whole-space and pairing data at order three -/

/--
Whole-space scalar-flux cancellation for every third velocity derivative
entering the top H³ transport block.
-/
def ThirdDerivativeTransportFluxVanishesAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : Prop :=
  ∀
    i k l j : PrimeTensor.Axis Depth.three,
      TransportScalarFluxVanishesAt
        v t
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (
                  spatial3.d
                    l
                    (
                      fun x =>
                        (v t x).component j
                    )
                )
            )
        )

/--
Integrability needed only to split the top H³ transport pairing into its
third-commutator and pure-transport pieces.
-/
def OrderThreeTransportPairingIntegrableAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : Prop :=
  ∀
    i k l j : PrimeTensor.Axis Depth.three,
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
                          (
                            fun y =>
                              (v t y).component j
                          )
                      )
                  )
                  x
                *
              thirdTransportCommutator
                  v t i k l j x
          )
        ∧
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
                          (
                            fun y =>
                              (v t y).component j
                          )
                      )
                  )
                  x
                *
              thirdTransportedDerivative
                  v t i k l j x
          )

/--
At derivative order three the pure transported third derivative cancels,
leaving exactly the third commutator pairing.
-/
theorem spatialEnergyPairing_momentumTransport3_eq_commutator
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
      hRegular :
        ThirdOrderTransportRegularityAt
          v t
    )
    (
      hFlux :
        ThirdDerivativeTransportFluxVanishesAt
          v t
    )
    (
      hInt :
        OrderThreeTransportPairingIntegrableAt
          v t
    )
    (i k l j : PrimeTensor.Axis Depth.three) :
    spatialEnergyPairing
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (
                  spatial3.d
                    l
                    (
                      fun x =>
                        (v t x).component j
                    )
                )
            )
        )
        (
          momentumTransport3Component
            v t i k l j
        )
      =
    spatialEnergyPairing
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (
                  spatial3.d
                    l
                    (
                      fun x =>
                        (v t x).component j
                    )
                )
            )
        )
        (
          thirdTransportCommutator
            v t i k l j
        ) := by

  rw [
    momentumTransport3Component_eq_commutator_add_transport
      s ht hRegular i k l j
  ]

  rw [
    spatialEnergyPairing_add_of_integrable
      (hInt i k l j).1
      (hInt i k l j).2
  ]

  have hF2 :
      SpatialC2
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (
                  fun x =>
                    (v t x).component j
                )
            )
        ) :=
    (hRegular k l j).2

  have hThird :
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
                    (
                      fun x =>
                        (v t x).component j
                    )
                )
            )
        ) :=
    firstPartial_spatialC1_of_spatialC2_orderThree
      hF2 i

  have hPure :
      spatialEnergyPairing
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (
                    spatial3.d
                      l
                      (
                        fun x =>
                          (v t x).component j
                      )
                  )
              )
          )
          (
            thirdTransportedDerivative
              v t i k l j
          )
        =
      0 := by

    unfold thirdTransportedDerivative

    exact
      spatialEnergyPairing_scalarTransport_eq_zero
        s
        ht
        hThird
        (hFlux i k l j)

  rw [hPure, add_zero]

/-! ## Logged H³ specialization -/

def H3OrderThreeTransportRegularityAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ThirdOrderTransportRegularityAt
    (
      PrimeTensor.Bridge.logSpaceTimeVectorField
        u
    )
    t

def H3ThirdDerivativeTransportFluxVanishesAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ThirdDerivativeTransportFluxVanishesAt
    (
      PrimeTensor.Bridge.logSpaceTimeVectorField
        u
    )
    t

def H3OrderThreeTransportPairingIntegrableAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  OrderThreeTransportPairingIntegrableAt
    (
      PrimeTensor.Bridge.logSpaceTimeVectorField
        u
    )
    t

/--
The complete order-three H³ transport derivative is the finite sum of genuine
third commutator pairings.
-/
theorem velocityH3TransportDerivative3At_eq_commutator
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
      hRegular :
        H3OrderThreeTransportRegularityAt
          u t
    )
    (
      hFlux :
        H3ThirdDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hInt :
        H3OrderThreeTransportPairingIntegrableAt
          u t
    ) :
    velocityH3TransportDerivative3At
        u t
      =
    ∑ j : PrimeTensor.Axis Depth.three,
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
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
              (
                thirdTransportCommutator
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j
              ) := by

  rcases hClass.pressure_witness with
    ⟨
      p,
      s,
      hp4
    ⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  unfold velocityH3TransportDerivative3At

  apply Finset.sum_congr rfl
  intro j hj

  apply Finset.sum_congr rfl
  intro i hi

  apply Finset.sum_congr rfl
  intro k hk

  apply Finset.sum_congr rfl
  intro l hl

  change
    spatialEnergyPairing
        (
          spatial3.d
            i
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
        )
        (
          momentumTransport3Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j
        )
      =
    spatialEnergyPairing
        (
          spatial3.d
            i
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
        )
        (
          thirdTransportCommutator
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j
        )

  exact
    spatialEnergyPairing_momentumTransport3_eq_commutator
      s
      htNS
      hRegular
      hFlux
      hInt
      i k l j

end Euclidean
end Bridge
end PrimeTensor
