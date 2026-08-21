import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.One

/-!
# Second-order transport commutator decomposition

Starting from the green first-order identity

    ∂ₖ ((v · ∇)vⱼ)
      =
    C₁(k,j) + v · ∇(∂ₖvⱼ),

differentiate once more in direction `i`.

The derivative of the pure transport term splits canonically as

    ∂ᵢ (v · ∇f)
      =
    (∂ᵢv · ∇)f + v · ∇(∂ᵢf).

Thus the order-two transport term is again

    second commutator + pure transport of ∂ᵢ∂ₖvⱼ.

The pure transport piece cancels under the same explicit whole-space scalar
flux condition used at order one.  No nonlinear L² estimate is assumed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderTwo
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-! ## Regularity helpers -/

private theorem firstPartial_spatialC1_of_spatialC2
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

private theorem firstPartial_spatialC2_of_spatialC3
    {f : ScalarField3}
    (
      hf :
        SpatialC3 f
    )
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC2
      (
        spatial3.d i f
      ) := by

  change
    SpatialC2
      (
        fun y =>
          partialDeriv i f y
      )

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hf i

private theorem h3ScalarTransport_spatialC1
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
    firstPartial_spatialC1_of_spatialC2
      hf xAxis

  have hfy :
      SpatialC1
        (
          spatial3.d yAxis f
        ) :=
    firstPartial_spatialC1_of_spatialC2
      hf yAxis

  have hfz :
      SpatialC1
        (
          spatial3.d zAxis f
        ) :=
    firstPartial_spatialC1_of_spatialC2
      hf zAxis

  unfold h3ScalarTransport

  exact
    (hux.mul hfx).add
      (
        (huy.mul hfy).add
          (huz.mul hfz)
      )

private theorem firstTransportCommutator_spatialC1
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
    (k j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        firstTransportCommutator
          v t k j
      ) := by

  have hkx :=
    s.velocity_firstPartial_spatialC1
      ht xAxis k

  have hky :=
    s.velocity_firstPartial_spatialC1
      ht yAxis k

  have hkz :=
    s.velocity_firstPartial_spatialC1
      ht zAxis k

  have hjx :=
    s.velocity_firstPartial_spatialC1
      ht j xAxis

  have hjy :=
    s.velocity_firstPartial_spatialC1
      ht j yAxis

  have hjz :=
    s.velocity_firstPartial_spatialC1
      ht j zAxis

  unfold firstTransportCommutator

  exact
    (hkx.mul hjx).add
      (
        (hky.mul hjy).add
          (hkz.mul hjz)
      )

private theorem firstTransportedDerivative_spatialC1
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
    (k j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        firstTransportedDerivative
          v t k j
      ) := by

  have h3 :
      SpatialC3
        (
          fun x =>
            (v t x).component j
        ) :=
    s.regularity.velocity_spatial_three
      t ht j

  have h2 :
      SpatialC2
        (
          spatial3.d
            k
            (
              fun x =>
                (v t x).component j
            )
        ) :=
    firstPartial_spatialC2_of_spatialC3
      h3 k

  unfold firstTransportedDerivative

  exact
    h3ScalarTransport_spatialC1
      s ht h2

/-! ## Differentiating transport of an arbitrary scalar -/

/--
The commutator created when one coordinate derivative hits the transporting
velocity in `v · ∇f`.
-/
noncomputable def scalarTransportDerivativeCommutator
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i : PrimeTensor.Axis Depth.three)
    (f : ScalarField3) :
    ScalarField3 :=
  fun x =>
    spatial3.d
        i
        (
          fun q =>
            (v t q).component xAxis
        )
        x
      *
    spatial3.d
        xAxis
        f
        x
      +
    (
      spatial3.d
          i
          (
            fun q =>
              (v t q).component yAxis
          )
          x
        *
      spatial3.d
          yAxis
          f
          x
        +
      spatial3.d
          i
          (
            fun q =>
              (v t q).component zAxis
          )
          x
        *
      spatial3.d
          zAxis
          f
          x
    )

/--
Exact derivative rule

    ∂ᵢ(v · ∇f)
      =
    (∂ᵢv · ∇)f
      +
    v · ∇(∂ᵢf).
-/
theorem spatial_d_h3ScalarTransport
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
    )
    (x : Point3)
    (i : PrimeTensor.Axis Depth.three) :
    spatial3.d
        i
        (
          h3ScalarTransport
            v t f
        )
        x
      =
    scalarTransportDerivativeCommutator
        v t i f x
      +
    h3ScalarTransport
        v t
        (
          spatial3.d i f
        )
        x := by

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
    firstPartial_spatialC1_of_spatialC2
      hf xAxis

  have hfy :
      SpatialC1
        (
          spatial3.d yAxis f
        ) :=
    firstPartial_spatialC1_of_spatialC2
      hf yAxis

  have hfz :
      SpatialC1
        (
          spatial3.d zAxis f
        ) :=
    firstPartial_spatialC1_of_spatialC2
      hf zAxis

  have hpx :
      SpatialC1
        (
          fun q =>
            (v t q).component xAxis
              *
            spatial3.d xAxis f q
        ) :=
    hux.mul hfx

  have hpy :
      SpatialC1
        (
          fun q =>
            (v t q).component yAxis
              *
            spatial3.d yAxis f q
        ) :=
    huy.mul hfy

  have hpz :
      SpatialC1
        (
          fun q =>
            (v t q).component zAxis
              *
            spatial3.d zAxis f q
        ) :=
    huz.mul hfz

  have hpyz :
      SpatialC1
        (
          fun q =>
            (v t q).component yAxis
                *
              spatial3.d yAxis f q
              +
            (v t q).component zAxis
                *
              spatial3.d zAxis f q
        ) :=
    hpy.add hpz

  have hcx :
      spatial3.d
          i
          (
            spatial3.d xAxis f
          )
          x
        =
      spatial3.d
          xAxis
          (
            spatial3.d i f
          )
          x := by

    simpa only [spatial3] using
      hf.spatial_d_comm
        x i xAxis

  have hcy :
      spatial3.d
          i
          (
            spatial3.d yAxis f
          )
          x
        =
      spatial3.d
          yAxis
          (
            spatial3.d i f
          )
          x := by

    simpa only [spatial3] using
      hf.spatial_d_comm
        x i yAxis

  have hcz :
      spatial3.d
          i
          (
            spatial3.d zAxis f
          )
          x
        =
      spatial3.d
          zAxis
          (
            spatial3.d i f
          )
          x := by

    simpa only [spatial3] using
      hf.spatial_d_comm
        x i zAxis

  unfold h3ScalarTransport

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hpx hpyz x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hux hfx x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hpy hpz x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      huy hfy x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      huz hfz x i,
    hcx,
    hcy,
    hcz
  ]

  unfold scalarTransportDerivativeCommutator

  ring

/-! ## Exact second-order split -/

/--
All non-pure-transport terms generated at derivative order two.
-/
noncomputable def secondTransportCommutator
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    spatial3.d
        i
        (
          firstTransportCommutator
            v t k j
        )
        x
      +
    scalarTransportDerivativeCommutator
        v t i
        (
          spatial3.d
            k
            (
              fun q =>
                (v t q).component j
            )
        )
        x

/--
The pure transported second derivative.
-/
noncomputable def secondTransportedDerivative
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k j : PrimeTensor.Axis Depth.three) :
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
              fun q =>
                (v t q).component j
            )
        )
    )

/--
Exact order-two transport decomposition.
-/
theorem momentumTransport2Component_eq_commutator_add_transport
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
    (i k j : PrimeTensor.Axis Depth.three) :
    momentumTransport2Component
        v t i k j
      =
    fun x =>
      secondTransportCommutator
          v t i k j x
        +
      secondTransportedDerivative
          v t i k j x := by

  have h3 :
      SpatialC3
        (
          fun x =>
            (v t x).component j
        ) :=
    s.regularity.velocity_spatial_three
      t ht j

  have h2 :
      SpatialC2
        (
          spatial3.d
            k
            (
              fun x =>
                (v t x).component j
            )
        ) :=
    firstPartial_spatialC2_of_spatialC3
      h3 k

  have hComm :
      SpatialC1
        (
          firstTransportCommutator
            v t k j
        ) :=
    firstTransportCommutator_spatialC1
      s ht k j

  have hPure :
      SpatialC1
        (
          firstTransportedDerivative
            v t k j
        ) :=
    firstTransportedDerivative_spatialC1
      s ht k j

  funext x

  unfold momentumTransport2Component

  rw [
    momentumTransport1Component_eq_commutator_add_transport
      s ht k j
  ]

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hComm hPure x i
  ]

  unfold firstTransportedDerivative

  rw [
    spatial_d_h3ScalarTransport
      s ht h2 x i
  ]

  unfold
    secondTransportCommutator
    secondTransportedDerivative

  ring

/-! ## Whole-space and pairing data at order two -/

def SecondDerivativeTransportFluxVanishesAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : Prop :=
  ∀
    i k j : PrimeTensor.Axis Depth.three,
      TransportScalarFluxVanishesAt
        v t
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (
                  fun x =>
                    (v t x).component j
                )
            )
        )

def OrderTwoTransportPairingIntegrableAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
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
                          (v t y).component j
                      )
                  )
                  x
                *
              secondTransportCommutator
                  v t i k j x
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
                        fun y =>
                          (v t y).component j
                      )
                  )
                  x
                *
              secondTransportedDerivative
                  v t i k j x
          )

/--
At order two the pure transported second derivative cancels, leaving exactly
the second commutator pairing.
-/
theorem spatialEnergyPairing_momentumTransport2_eq_commutator
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
      hFlux :
        SecondDerivativeTransportFluxVanishesAt
          v t
    )
    (
      hInt :
        OrderTwoTransportPairingIntegrableAt
          v t
    )
    (i k j : PrimeTensor.Axis Depth.three) :
    spatialEnergyPairing
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (
                  fun x =>
                    (v t x).component j
                )
            )
        )
        (
          momentumTransport2Component
            v t i k j
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
                  fun x =>
                    (v t x).component j
                )
            )
        )
        (
          secondTransportCommutator
            v t i k j
        ) := by

  rw [
    momentumTransport2Component_eq_commutator_add_transport
      s ht i k j
  ]

  rw [
    spatialEnergyPairing_add_of_integrable
      (hInt i k j).1
      (hInt i k j).2
  ]

  have h3 :
      SpatialC3
        (
          fun x =>
            (v t x).component j
        ) :=
    s.regularity.velocity_spatial_three
      t ht j

  have h2 :
      SpatialC2
        (
          spatial3.d
            k
            (
              fun x =>
                (v t x).component j
            )
        ) :=
    firstPartial_spatialC2_of_spatialC3
      h3 k

  have hSecond :
      SpatialC1
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (
                  fun x =>
                    (v t x).component j
                )
            )
        ) :=
    firstPartial_spatialC1_of_spatialC2
      h2 i

  have hPure :
      spatialEnergyPairing
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (
                    fun x =>
                      (v t x).component j
                  )
              )
          )
          (
            secondTransportedDerivative
              v t i k j
          )
        =
      0 := by

    unfold secondTransportedDerivative

    exact
      spatialEnergyPairing_scalarTransport_eq_zero
        s
        ht
        hSecond
        (hFlux i k j)

  rw [hPure, add_zero]

/-! ## Logged H³ specialization -/

def H3SecondDerivativeTransportFluxVanishesAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  SecondDerivativeTransportFluxVanishesAt
    (
      PrimeTensor.Bridge.logSpaceTimeVectorField
        u
    )
    t

def H3OrderTwoTransportPairingIntegrableAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  OrderTwoTransportPairingIntegrableAt
    (
      PrimeTensor.Bridge.logSpaceTimeVectorField
        u
    )
    t

/--
The complete order-two H³ transport derivative is the finite sum of second
commutator pairings.
-/
theorem velocityH3TransportDerivative2At_eq_commutator
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
      hFlux :
        H3SecondDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hInt :
        H3OrderTwoTransportPairingIntegrableAt
          u t
    ) :
    velocityH3TransportDerivative2At
        u t
      =
    ∑ j : PrimeTensor.Axis Depth.three,
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          spatialEnergyPairing
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
            )
            (
              secondTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k j
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

  unfold velocityH3TransportDerivative2At

  apply Finset.sum_congr rfl
  intro j hj

  apply Finset.sum_congr rfl
  intro i hi

  apply Finset.sum_congr rfl
  intro k hk

  change
    spatialEnergyPairing
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (
                  fun x =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t x
                    ).component j
                )
            )
        )
        (
          momentumTransport2Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k j
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
                  fun x =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t x
                    ).component j
                )
            )
        )
        (
          secondTransportCommutator
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k j
        )

  exact
    spatialEnergyPairing_momentumTransport2_eq_commutator
      s
      htNS
      hFlux
      hInt
      i k j

end Euclidean
end Bridge
end PrimeTensor
