import PrimeTensor.Fluid.VorticityH3EnergyTransportCancellation

/-!
# First-order transport commutator decomposition

The order-zero incompressible transport cancellation is already available in
`VorticityH3EnergyTransportCancellation`.

At first spatial order one has the exact identity

    ∂ᵢ ((v · ∇) vⱼ)
      =
    (∂ᵢ v · ∇) vⱼ
      +
    v · ∇(∂ᵢ vⱼ).

The second term is again a pure transport term and cancels in the energy
pairing.  This file proves that statement in the project's explicit
three-coordinate differential language.

No L² estimate is asserted here.  The only analytic hypotheses are the
whole-space scalar-flux condition and the integrability required to split the
energy pairing across the two summands.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderOne
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-! ## Generic scalar transport by a three-dimensional velocity field -/

/--
Transport of an arbitrary scalar field `f` by the velocity `v(t)`.
-/
noncomputable def h3ScalarTransport
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (f : ScalarField3) :
    ScalarField3 :=
  fun x =>
    (v t x).component xAxis
        *
      spatial3.d xAxis f x
      +
    (
      (v t x).component yAxis
          *
        spatial3.d yAxis f x
        +
      (v t x).component zAxis
          *
        spatial3.d zAxis f x
    )

/--
Coordinate divergence of the scalar-energy flux `v f²`.
-/
noncomputable def transportScalarFluxDivergenceXYZ
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (f : ScalarField3)
    (x : Point3) : ℝ :=
  spatial3.d
      xAxis
      (
        fun q =>
          (v t q).component xAxis
            *
          (f q * f q)
      )
      x
    +
  (
    spatial3.d
        yAxis
        (
          fun q =>
            (v t q).component yAxis
              *
            (f q * f q)
        )
        x
      +
    spatial3.d
        zAxis
        (
          fun q =>
            (v t q).component zAxis
              *
            (f q * f q)
        )
        x
  )

/--
Whole-space boundary/decay datum for one transported scalar field.
-/
def TransportScalarFluxVanishesAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (f : ScalarField3) : Prop :=
  (
    ∫ x : Point3,
      transportScalarFluxDivergenceXYZ
        v t f x
  )
    =
  0

/--
For an incompressible velocity, `div(v f²) = 2 f (v · ∇f)`.
-/
theorem transportScalarFluxDivergenceXYZ_eq_two_mul_transport
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
        SpatialC1 f
    )
    (x : Point3) :
    transportScalarFluxDivergenceXYZ
        v t f x
      =
    2
      * f x
      * h3ScalarTransport
          v t f x := by

  have hux :
      SpatialC1
        (
          fun q =>
            (v t q).component xAxis
        ) :=
    s.velocity_component_spatialC1
      ht xAxis

  have huy :
      SpatialC1
        (
          fun q =>
            (v t q).component yAxis
        ) :=
    s.velocity_component_spatialC1
      ht yAxis

  have huz :
      SpatialC1
        (
          fun q =>
            (v t q).component zAxis
        ) :=
    s.velocity_component_spatialC1
      ht zAxis

  have hf2 :
      SpatialC1
        (
          fun q =>
            f q * f q
        ) :=
    hf.mul hf

  have hDiv :
      spatial3.d
          xAxis
          (
            fun q =>
              (v t q).component xAxis
          )
          x
        +
      (
        spatial3.d
            yAxis
            (
              fun q =>
                (v t q).component yAxis
            )
            x
          +
        spatial3.d
            zAxis
            (
              fun q =>
                (v t q).component zAxis
            )
            x
      )
        =
      0 :=
    s.incompressible_xyz
      ht x

  unfold
    transportScalarFluxDivergenceXYZ
    h3ScalarTransport

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hux hf2 x xAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      huy hf2 x yAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      huz hf2 x zAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hf hf x xAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hf hf x yAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hf hf x zAxis
  ]

  nlinarith [hDiv]

/--
The generic scalar pure-transport energy pairing vanishes under the explicit
whole-space flux condition.
-/
theorem spatialEnergyPairing_scalarTransport_eq_zero
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
        SpatialC1 f
    )
    (
      hFlux :
        TransportScalarFluxVanishesAt
          v t f
    ) :
    spatialEnergyPairing
        f
        (h3ScalarTransport v t f)
      =
    0 := by

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

  have hIntegral :
      (
        ∫ x : Point3,
          2
            *
          (
            f x
              *
            h3ScalarTransport
              v t f x
          )
      )
        =
      0 := by

    rw [
      ← hPointwise
    ]

    exact hFlux

  unfold spatialEnergyPairing

  rw [
    ← MeasureTheory.integral_const_mul
  ]

  exact hIntegral

/-! ## Pairing linearity with explicit integrability -/

/--
Split one scalar energy pairing across an additive target.
-/
theorem spatialEnergyPairing_add_of_integrable
    {
      f g q :
        ScalarField3
    }
    (
      hg :
        MeasureTheory.Integrable
          (
            fun x : Point3 =>
              f x * g x
          )
    )
    (
      hq :
        MeasureTheory.Integrable
          (
            fun x : Point3 =>
              f x * q x
          )
    ) :
    spatialEnergyPairing
        f
        (
          fun x =>
            g x + q x
        )
      =
    spatialEnergyPairing f g
      +
    spatialEnergyPairing f q := by

  unfold spatialEnergyPairing

  have hPointwise :
      (
        fun x : Point3 =>
          f x * (g x + q x)
      )
        =
      (
        fun x : Point3 =>
          f x * g x
            +
          f x * q x
      ) := by

    funext x
    ring

  rw [
    hPointwise,
    MeasureTheory.integral_add
      hg hq
  ]

  ring

/-! ## Exact first-order differentiated-advection decomposition -/

/--
The first-order commutator `(∂ᵢv · ∇)vⱼ`.
-/
noncomputable def firstTransportCommutator
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i j : PrimeTensor.Axis Depth.three) :
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
        (
          fun q =>
            (v t q).component j
        )
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
          (
            fun q =>
              (v t q).component j
          )
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
          (
            fun q =>
              (v t q).component j
          )
          x
    )

/--
The pure transported first derivative `v · ∇(∂ᵢvⱼ)`.
-/
noncomputable def firstTransportedDerivative
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  h3ScalarTransport
    v t
    (
      spatial3.d
        i
        (
          fun q =>
            (v t q).component j
        )
    )

/--
Exact first-order differentiated-advection split.
-/
theorem momentumTransport1Component_eq_commutator_add_transport
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
    (i j : PrimeTensor.Axis Depth.three) :
    momentumTransport1Component
        v t i j
      =
    fun x =>
      firstTransportCommutator
          v t i j x
        +
      firstTransportedDerivative
          v t i j x := by

  funext x

  have hProduct :=
    s.spatial_d_realAdvectionComponent
      ht x i j

  have hcx :=
    s.velocity_spatial_d_comm
      ht x j i xAxis

  have hcy :=
    s.velocity_spatial_d_comm
      ht x j i yAxis

  have hcz :=
    s.velocity_spatial_d_comm
      ht x j i zAxis

  unfold
    momentumTransport1Component
    momentumTransport0Component

  rw [
    hProduct,
    hcx,
    hcy,
    hcz
  ]

  unfold
    firstTransportCommutator
    firstTransportedDerivative
    h3ScalarTransport

  ring

/-! ## Whole-space and integrability data for order one -/

/--
Whole-space scalar-flux cancellation for every first derivative entering the
order-one H³ transport block.
-/
def FirstDerivativeTransportFluxVanishesAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : Prop :=
  ∀
    i j : PrimeTensor.Axis Depth.three,
      TransportScalarFluxVanishesAt
        v t
        (
          spatial3.d
            i
            (
              fun x =>
                (v t x).component j
            )
        )

/--
Integrability needed solely to split the order-one pairing into commutator and
pure-transport pieces.
-/
def OrderOneTransportPairingIntegrableAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
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
                      (v t y).component j
                  )
                  x
                *
              firstTransportCommutator
                  v t i j x
          )
        ∧
      MeasureTheory.Integrable
          (
            fun x : Point3 =>
              spatial3.d
                  i
                  (
                    fun y =>
                      (v t y).component j
                  )
                  x
                *
              firstTransportedDerivative
                  v t i j x
          )

/--
At first order, after the pure transported derivative cancels, the energy
pairing is exactly the commutator pairing.
-/
theorem spatialEnergyPairing_momentumTransport1_eq_commutator
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
        FirstDerivativeTransportFluxVanishesAt
          v t
    )
    (
      hInt :
        OrderOneTransportPairingIntegrableAt
          v t
    )
    (i j : PrimeTensor.Axis Depth.three) :
    spatialEnergyPairing
        (
          spatial3.d
            i
            (
              fun x =>
                (v t x).component j
            )
        )
        (
          momentumTransport1Component
            v t i j
        )
      =
    spatialEnergyPairing
        (
          spatial3.d
            i
            (
              fun x =>
                (v t x).component j
            )
        )
        (
          firstTransportCommutator
            v t i j
        ) := by

  rw [
    momentumTransport1Component_eq_commutator_add_transport
      s ht i j
  ]

  rw [
    spatialEnergyPairing_add_of_integrable
      (hInt i j).1
      (hInt i j).2
  ]

  have hPure :
      spatialEnergyPairing
          (
            spatial3.d
              i
              (
                fun x =>
                  (v t x).component j
              )
          )
          (
            firstTransportedDerivative
              v t i j
          )
        =
      0 := by

    unfold firstTransportedDerivative

    exact
      spatialEnergyPairing_scalarTransport_eq_zero
        s
        ht
        (s.velocity_firstPartial_spatialC1
          ht j i)
        (hFlux i j)

  rw [hPure, add_zero]

/-! ## Logged H³ specialization -/

def H3FirstDerivativeTransportFluxVanishesAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  FirstDerivativeTransportFluxVanishesAt
    (
      PrimeTensor.Bridge.logSpaceTimeVectorField
        u
    )
    t

def H3OrderOneTransportPairingIntegrableAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  OrderOneTransportPairingIntegrableAt
    (
      PrimeTensor.Bridge.logSpaceTimeVectorField
        u
    )
    t

/--
The complete order-one H³ transport derivative is exactly the finite sum of
the first commutator pairings.
-/
theorem velocityH3TransportDerivative1At_eq_commutator
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
        H3FirstDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hInt :
        H3OrderOneTransportPairingIntegrableAt
          u t
    ) :
    velocityH3TransportDerivative1At
        u t
      =
    ∑ j : PrimeTensor.Axis Depth.three,
      ∑ i : PrimeTensor.Axis Depth.three,
        spatialEnergyPairing
          (
            spatial3.d
              i
              (loggedVelocityComponent u t j)
          )
          (
            firstTransportCommutator
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i j
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

  unfold velocityH3TransportDerivative1At

  apply Finset.sum_congr rfl
  intro j hj

  apply Finset.sum_congr rfl
  intro i hi

  change
    spatialEnergyPairing
        (
          spatial3.d
            i
            (
              fun x =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t x
                ).component j
            )
        )
        (
          momentumTransport1Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i j
        )
      =
    spatialEnergyPairing
        (
          spatial3.d
            i
            (
              fun x =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t x
                ).component j
            )
        )
        (
          firstTransportCommutator
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i j
        )

  exact
    spatialEnergyPairing_momentumTransport1_eq_commutator
      s
      htNS
      hFlux
      hInt
      i j

end Euclidean
end Bridge
end PrimeTensor
