import PrimeTensor.Fluid.VorticityH3EnergyPDEDecomposition

/-!
# Diffusion / transport / pressure split of the canonical H³ derivative

After exact Navier--Stokes substitution, the canonical H³ derivative is a
finite sum of pairings against momentum right-hand sides.

This file splits that quantity into three scalar contributions:

    diffusion - transport - pressure.

Two logically different ingredients are kept explicit:

* orders zero and one split definitionally from the existing momentum formulas;
* orders two and three require spatial derivative linearity through subtraction.

Lebesgue integral linearity also requires integrability of the three product
integrands in each pairing.  Those hypotheses are packaged explicitly rather
than hidden.

The final theorem is exact algebra: once the higher-order field splits and the
pairing integrability hypotheses hold,

    velocityH3PDEDerivativeAt
      = velocityH3DiffusionDerivativeAt
        - velocityH3TransportDerivativeAt
        - velocityH3PressureDerivativeAt.

The next analytic steps can therefore attack the three pieces independently.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3PDESplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-! ## Component fields -/

noncomputable def momentumDiffusion0Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  PrimeTensor.Bridge.RealFluid.laplacian
    spatial3
    (fun y =>
      (v t y).component j)

noncomputable def momentumTransport0Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    realAdvectionComponent
      v t x j

noncomputable def momentumPressure0Component
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    j
    (p t)

noncomputable def momentumDiffusion1Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (momentumDiffusion0Component v t j)

noncomputable def momentumTransport1Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (momentumTransport0Component v t j)

noncomputable def momentumPressure1Component
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (momentumPressure0Component p t j)

noncomputable def momentumDiffusion2Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (momentumDiffusion1Component v t k j)

noncomputable def momentumTransport2Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (momentumTransport1Component v t k j)

noncomputable def momentumPressure2Component
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (momentumPressure1Component p t k j)

noncomputable def momentumDiffusion3Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (
      spatial3.d
        k
        (momentumDiffusion1Component v t l j)
    )

noncomputable def momentumTransport3Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (
      spatial3.d
        k
        (momentumTransport1Component v t l j)
    )

noncomputable def momentumPressure3Component
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (
      spatial3.d
        k
        (momentumPressure1Component p t l j)
    )

/-! ## Field-level splits -/

theorem momentumRHS0Component_eq_split
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
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    momentumRHS0Component v p t j
      =
    fun x =>
      momentumDiffusion0Component v t j x
        -
      momentumTransport0Component v t j x
        -
      momentumPressure0Component p t j x := by

  rfl

theorem momentumRHS1Component_eq_split
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
    (t : ℝ)
    (i j : PrimeTensor.Axis Depth.three) :
    momentumRHS1Component v p t i j
      =
    fun x =>
      momentumDiffusion1Component v t i j x
        -
      momentumTransport1Component v t i j x
        -
      momentumPressure1Component p t i j x := by

  rfl

/--
The only field-level algebra still needed for the higher orders: distribute
spatial derivatives through the two subtractions.
-/
def HigherOrderMomentumRHSSplitsAt
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
      i k j : PrimeTensor.Axis Depth.three,
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
              p t i k j x
  )
    ∧
  (
    ∀
      i k l j : PrimeTensor.Axis Depth.three,
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
              p t i k l j x
  )

/-! ## Pairing linearity -/

/--
Minimal integrability required to split one energy pairing against
`d - q - r`.
-/
def SpatialEnergyPairingTripletIntegrable
    (f d q r : ScalarField3) : Prop :=
  MeasureTheory.Integrable
      (fun x : Point3 =>
        f x * d x)
    ∧
  MeasureTheory.Integrable
      (fun x : Point3 =>
        f x * q x)
    ∧
  MeasureTheory.Integrable
      (fun x : Point3 =>
        f x * r x)

theorem spatialEnergyPairing_sub_sub
    {
      f d q r :
        ScalarField3
    }
    (
      hInt :
        SpatialEnergyPairingTripletIntegrable
          f d q r
    ) :
    spatialEnergyPairing
        f
        (fun x =>
          d x - q x - r x)
      =
    spatialEnergyPairing f d
      -
    spatialEnergyPairing f q
      -
    spatialEnergyPairing f r := by

  rcases hInt with
    ⟨
      hd,
      hq,
      hr
    ⟩

  unfold spatialEnergyPairing

  have hPointwise :
      (
        fun x : Point3 =>
          f x * (d x - q x - r x)
      )
        =
      (
        fun x : Point3 =>
          (f x * d x - f x * q x)
            -
          f x * r x
      ) := by

    funext x
    ring

  rw [hPointwise]

  have hSubDQ :
      (∫ x : Point3,
          f x * d x - f x * q x)
        =
      (∫ x : Point3, f x * d x)
        -
      (∫ x : Point3, f x * q x) :=
    MeasureTheory.integral_sub
      hd
      hq

  have hSubDQR :
      (∫ x : Point3,
          (f x * d x - f x * q x) - f x * r x)
        =
      (∫ x : Point3,
          f x * d x - f x * q x)
        -
      (∫ x : Point3, f x * r x) :=
    MeasureTheory.integral_sub
      (hd.sub hq)
      hr

  rw [
    hSubDQR,
    hSubDQ
  ]

  ring

/-! ## Scalar contributions -/

noncomputable def velocityH3DiffusionDerivative0At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    spatialEnergyPairing
      (loggedVelocityComponent u t j)
      (
        momentumDiffusion0Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t j
      )

noncomputable def velocityH3TransportDerivative0At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    spatialEnergyPairing
      (loggedVelocityComponent u t j)
      (
        momentumTransport0Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t j
      )

noncomputable def velocityH3PressureDerivative0At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    spatialEnergyPairing
      (loggedVelocityComponent u t j)
      (momentumPressure0Component p t j)

noncomputable def velocityH3DiffusionDerivative1At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      spatialEnergyPairing
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        )
        (
          momentumDiffusion1Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i j
        )

noncomputable def velocityH3TransportDerivative1At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      spatialEnergyPairing
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        )
        (
          momentumTransport1Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i j
        )

noncomputable def velocityH3PressureDerivative1At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      spatialEnergyPairing
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        )
        (momentumPressure1Component p t i j)

noncomputable def velocityH3DiffusionDerivative2At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
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
            momentumDiffusion2Component
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k j
          )

noncomputable def velocityH3TransportDerivative2At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
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
            momentumTransport2Component
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k j
          )

noncomputable def velocityH3PressureDerivative2At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : ℝ :=
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
          (momentumPressure2Component p t i k j)

noncomputable def velocityH3DiffusionDerivative3At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
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
              momentumDiffusion3Component
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j
            )

noncomputable def velocityH3TransportDerivative3At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
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
              momentumTransport3Component
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j
            )

noncomputable def velocityH3PressureDerivative3At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : ℝ :=
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
            (momentumPressure3Component p t i k l j)

noncomputable def velocityH3DiffusionDerivativeAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  velocityH3DiffusionDerivative0At u t
    + velocityH3DiffusionDerivative1At u t
    + velocityH3DiffusionDerivative2At u t
    + velocityH3DiffusionDerivative3At u t

noncomputable def velocityH3TransportDerivativeAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  velocityH3TransportDerivative0At u t
    + velocityH3TransportDerivative1At u t
    + velocityH3TransportDerivative2At u t
    + velocityH3TransportDerivative3At u t

noncomputable def velocityH3PressureDerivativeAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : ℝ :=
  velocityH3PressureDerivative0At u p t
    + velocityH3PressureDerivative1At u p t
    + velocityH3PressureDerivative2At u p t
    + velocityH3PressureDerivative3At u p t

/-! ## Pairing-integrability package -/

def H3PDEPairingIntegrableAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : Prop :=
  let v :=
    PrimeTensor.Bridge.logSpaceTimeVectorField u

  (
    ∀ j : PrimeTensor.Axis Depth.three,
      SpatialEnergyPairingTripletIntegrable
        (loggedVelocityComponent u t j)
        (momentumDiffusion0Component v t j)
        (momentumTransport0Component v t j)
        (momentumPressure0Component p t j)
  )
    ∧
  (
    ∀
      i j : PrimeTensor.Axis Depth.three,
      SpatialEnergyPairingTripletIntegrable
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        )
        (momentumDiffusion1Component v t i j)
        (momentumTransport1Component v t i j)
        (momentumPressure1Component p t i j)
  )
    ∧
  (
    ∀
      i k j : PrimeTensor.Axis Depth.three,
      SpatialEnergyPairingTripletIntegrable
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (loggedVelocityComponent u t j)
            )
        )
        (momentumDiffusion2Component v t i k j)
        (momentumTransport2Component v t i k j)
        (momentumPressure2Component p t i k j)
  )
    ∧
  (
    ∀
      i k l j : PrimeTensor.Axis Depth.three,
      SpatialEnergyPairingTripletIntegrable
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
        (momentumDiffusion3Component v t i k l j)
        (momentumTransport3Component v t i k l j)
        (momentumPressure3Component p t i k l j)
  )

/-! ## Orderwise scalar splits -/

theorem velocityH3PDEDerivative0At_eq_split
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
      hInt :
        H3PDEPairingIntegrableAt
          u p t
    ) :
    velocityH3PDEDerivative0At u p t
      =
    velocityH3DiffusionDerivative0At u t
      -
    velocityH3TransportDerivative0At u t
      -
    velocityH3PressureDerivative0At u p t := by

  rcases hInt with
    ⟨h0, h1, h2, h3⟩

  unfold
    velocityH3PDEDerivative0At
    velocityH3DiffusionDerivative0At
    velocityH3TransportDerivative0At
    velocityH3PressureDerivative0At

  calc
    (∑ j,
      spatialEnergyPairing
        (loggedVelocityComponent u t j)
        (
          momentumRHS0Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            p t j
        ))
        =
      ∑ j,
        (
          spatialEnergyPairing
            (loggedVelocityComponent u t j)
            (
              momentumDiffusion0Component
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t j
            )
            -
          spatialEnergyPairing
            (loggedVelocityComponent u t j)
            (
              momentumTransport0Component
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t j
            )
            -
          spatialEnergyPairing
            (loggedVelocityComponent u t j)
            (momentumPressure0Component p t j)
        ) := by

      apply Finset.sum_congr rfl

      intro j hj

      rw [momentumRHS0Component_eq_split]

      exact
        spatialEnergyPairing_sub_sub
          (h0 j)

    _ =
      (∑ j,
        spatialEnergyPairing
          (loggedVelocityComponent u t j)
          (
            momentumDiffusion0Component
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t j
          ))
        -
      (∑ j,
        spatialEnergyPairing
          (loggedVelocityComponent u t j)
          (
            momentumTransport0Component
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t j
          ))
        -
      (∑ j,
        spatialEnergyPairing
          (loggedVelocityComponent u t j)
          (momentumPressure0Component p t j)) := by

      rw [
        Finset.sum_sub_distrib,
        Finset.sum_sub_distrib
      ]

theorem velocityH3PDEDerivative1At_eq_split
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
      hInt :
        H3PDEPairingIntegrableAt
          u p t
    ) :
    velocityH3PDEDerivative1At u p t
      =
    velocityH3DiffusionDerivative1At u t
      -
    velocityH3TransportDerivative1At u t
      -
    velocityH3PressureDerivative1At u p t := by

  rcases hInt with
    ⟨h0, h1, h2, h3⟩

  unfold
    velocityH3PDEDerivative1At
    velocityH3DiffusionDerivative1At
    velocityH3TransportDerivative1At
    velocityH3PressureDerivative1At

  calc
    (∑ j,
      ∑ i,
        spatialEnergyPairing
          (
            spatial3.d
              i
              (loggedVelocityComponent u t j)
          )
          (
            momentumRHS1Component
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              p t i j
          ))
        =
      ∑ j,
        ∑ i,
          (
            spatialEnergyPairing
              (
                spatial3.d
                  i
                  (loggedVelocityComponent u t j)
              )
              (
                momentumDiffusion1Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i j
              )
              -
            spatialEnergyPairing
              (
                spatial3.d
                  i
                  (loggedVelocityComponent u t j)
              )
              (
                momentumTransport1Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i j
              )
              -
            spatialEnergyPairing
              (
                spatial3.d
                  i
                  (loggedVelocityComponent u t j)
              )
              (momentumPressure1Component p t i j)
          ) := by

      apply Finset.sum_congr rfl
      intro j hj

      apply Finset.sum_congr rfl
      intro i hi

      rw [momentumRHS1Component_eq_split]

      exact
        spatialEnergyPairing_sub_sub
          (h1 i j)

    _ =
      (∑ j,
        ∑ i,
          spatialEnergyPairing
            (
              spatial3.d
                i
                (loggedVelocityComponent u t j)
            )
            (
              momentumDiffusion1Component
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i j
            ))
        -
      (∑ j,
        ∑ i,
          spatialEnergyPairing
            (
              spatial3.d
                i
                (loggedVelocityComponent u t j)
            )
            (
              momentumTransport1Component
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i j
            ))
        -
      (∑ j,
        ∑ i,
          spatialEnergyPairing
            (
              spatial3.d
                i
                (loggedVelocityComponent u t j)
            )
            (momentumPressure1Component p t i j)) := by

      simp only [Finset.sum_sub_distrib]

theorem velocityH3PDEDerivative2At_eq_split
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
      hHigher :
        HigherOrderMomentumRHSSplitsAt
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
    velocityH3PDEDerivative2At u p t
      =
    velocityH3DiffusionDerivative2At u t
      -
    velocityH3TransportDerivative2At u t
      -
    velocityH3PressureDerivative2At u p t := by

  rcases hHigher with
    ⟨hSplit2, hSplit3⟩

  rcases hInt with
    ⟨h0, h1, h2, h3⟩

  unfold
    velocityH3PDEDerivative2At
    velocityH3DiffusionDerivative2At
    velocityH3TransportDerivative2At
    velocityH3PressureDerivative2At

  calc
    (∑ j,
      ∑ i,
        ∑ k,
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
              momentumRHS2Component
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                p t i k j
            ))
        =
      ∑ j,
        ∑ i,
          ∑ k,
            (
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
                  momentumDiffusion2Component
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u
                    )
                    t i k j
                )
                -
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
                  momentumTransport2Component
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u
                    )
                    t i k j
                )
                -
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
                (momentumPressure2Component p t i k j)
            ) := by

      apply Finset.sum_congr rfl
      intro j hj

      apply Finset.sum_congr rfl
      intro i hi

      apply Finset.sum_congr rfl
      intro k hk

      rw [hSplit2 i k j]

      exact
        spatialEnergyPairing_sub_sub
          (h2 i k j)

    _ =
      (∑ j,
        ∑ i,
          ∑ k,
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
                momentumDiffusion2Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k j
              ))
        -
      (∑ j,
        ∑ i,
          ∑ k,
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
                momentumTransport2Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k j
              ))
        -
      (∑ j,
        ∑ i,
          ∑ k,
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
              (momentumPressure2Component p t i k j)) := by

      simp only [Finset.sum_sub_distrib]

theorem velocityH3PDEDerivative3At_eq_split
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
      hHigher :
        HigherOrderMomentumRHSSplitsAt
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
    velocityH3PDEDerivative3At u p t
      =
    velocityH3DiffusionDerivative3At u t
      -
    velocityH3TransportDerivative3At u t
      -
    velocityH3PressureDerivative3At u p t := by

  rcases hHigher with
    ⟨hSplit2, hSplit3⟩

  rcases hInt with
    ⟨h0, h1, h2, h3⟩

  unfold
    velocityH3PDEDerivative3At
    velocityH3DiffusionDerivative3At
    velocityH3TransportDerivative3At
    velocityH3PressureDerivative3At

  calc
    (∑ j,
      ∑ i,
        ∑ k,
          ∑ l,
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
                momentumRHS3Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  p t i k l j
              ))
        =
      ∑ j,
        ∑ i,
          ∑ k,
            ∑ l,
              (
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
                    momentumDiffusion3Component
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u
                      )
                      t i k l j
                  )
                  -
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
                    momentumTransport3Component
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u
                      )
                      t i k l j
                  )
                  -
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
                  (momentumPressure3Component p t i k l j)
              ) := by

      apply Finset.sum_congr rfl
      intro j hj

      apply Finset.sum_congr rfl
      intro i hi

      apply Finset.sum_congr rfl
      intro k hk

      apply Finset.sum_congr rfl
      intro l hl

      rw [hSplit3 i k l j]

      exact
        spatialEnergyPairing_sub_sub
          (h3 i k l j)

    _ =
      (∑ j,
        ∑ i,
          ∑ k,
            ∑ l,
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
                  momentumDiffusion3Component
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u
                    )
                    t i k l j
                ))
        -
      (∑ j,
        ∑ i,
          ∑ k,
            ∑ l,
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
                  momentumTransport3Component
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u
                    )
                    t i k l j
                ))
        -
      (∑ j,
        ∑ i,
          ∑ k,
            ∑ l,
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
                (momentumPressure3Component p t i k l j)) := by

      simp only [Finset.sum_sub_distrib]

/--
Exact scalar diffusion / transport / pressure decomposition of the full
canonical PDE energy derivative.
-/
theorem velocityH3PDEDerivativeAt_eq_split
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
      hHigher :
        HigherOrderMomentumRHSSplitsAt
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

  unfold
    velocityH3PDEDerivativeAt
    velocityH3DiffusionDerivativeAt
    velocityH3TransportDerivativeAt
    velocityH3PressureDerivativeAt

  rw [
    velocityH3PDEDerivative0At_eq_split
      hInt,
    velocityH3PDEDerivative1At_eq_split
      hInt,
    velocityH3PDEDerivative2At_eq_split
      hHigher hInt,
    velocityH3PDEDerivative3At_eq_split
      hHigher hInt
  ]

  ring

/--
Combining canonical differentiation, Navier--Stokes substitution, and the
three-way scalar split.
-/
theorem deriv_velocityH3EnergyAt_eq_diffusion_sub_transport_sub_pressure
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
      hHigher :
        HigherOrderMomentumRHSSplitsAt
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

  calc
    deriv
        (velocityH3EnergyAt u)
        t
        =
      velocityH3PDEDerivativeAt
        u p t :=
      deriv_velocityH3EnergyAt_eq_pde
        s ht hDerivative

    _ =
      velocityH3DiffusionDerivativeAt u t
        -
      velocityH3TransportDerivativeAt u t
        -
      velocityH3PressureDerivativeAt u p t :=
      velocityH3PDEDerivativeAt_eq_split
        hHigher hInt

end Euclidean
end Bridge
end PrimeTensor
