import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Two.Expansion

/-!
# Explicit third-order H³ transport commutator expansion

The order-three transport module already proves that the pure transported third
derivative cancels, leaving the genuine third commutator. This file exposes
that commutator into the derivative-order classes needed for the analytic
estimate.

For one velocity axis `r`, the order-two commutator block is

    (D_k D_l u_r)(D_r u_j)
  + (D_l u_r)(D_k D_r u_j)
  + (D_k u_r)(D_r D_l u_j).

Differentiating in direction `i` and adding the scalar transport commutator
produces seven terms: four of type `D³u · Du` and three of type
`D²u · D²u`. Across the three coordinate axes this is the promised 21-term
expansion. No estimate is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

noncomputable local instance axisFintypeH3EnergyTransportOrderThreeExpansion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

private theorem velocitySecondPartial_spatialC1_orderThreeExpansion
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
    (j a b : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        spatial3.d
          a
          (
            spatial3.d
              b
              (
                fun q =>
                  (v t q).component j
              )
          )
      ) := by

  have h3 :
      SpatialC3
        (
          fun q =>
            (v t q).component j
        ) :=
    s.regularity.velocity_spatial_three
      t ht j

  have h2 :
      SpatialC2
        (
          spatial3.d
            b
            (
              fun q =>
                (v t q).component j
            )
        ) := by

    change
      SpatialC2
        (
          fun q =>
            partialDeriv
              b
              (
                fun y =>
                  (v t y).component j
              )
              q
        )

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
        h3 b

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      h2 a

noncomputable def secondTransportCommutatorAxisBlock
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (k l j r : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    (
      spatial3.d
          k
          (
            spatial3.d
              l
              (
                fun q =>
                  (v t q).component r
              )
          )
          x
        *
      spatial3.d
          r
          (
            fun q =>
              (v t q).component j
          )
          x
    )
      +
    (
      spatial3.d
          l
          (
            fun q =>
              (v t q).component r
          )
          x
        *
      spatial3.d
          k
          (
            spatial3.d
              r
              (
                fun q =>
                  (v t q).component j
              )
          )
          x
    )
      +
    (
      spatial3.d
          k
          (
            fun q =>
              (v t q).component r
          )
          x
        *
      spatial3.d
          r
          (
            spatial3.d
              l
              (
                fun q =>
                  (v t q).component j
              )
          )
          x
    )

theorem secondTransportCommutatorExpanded_eq_axisBlocks
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    (t : ℝ)
    (x : Point3)
    (k l j : PrimeTensor.Axis Depth.three) :
    secondTransportCommutatorExpanded
        v t k l j x
      =
    secondTransportCommutatorAxisBlock
        v t k l j xAxis x
      +
    (
      secondTransportCommutatorAxisBlock
          v t k l j yAxis x
        +
      secondTransportCommutatorAxisBlock
          v t k l j zAxis x
    ) := by

  unfold
    secondTransportCommutatorExpanded
    secondTransportCommutatorAxisBlock

  ring

private theorem secondTransportCommutatorAxisBlock_spatialC1
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
    (k l j r : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        secondTransportCommutatorAxisBlock
          v t k l j r
      ) := by

  have hklr :=
    velocitySecondPartial_spatialC1_orderThreeExpansion
      s ht r k l

  have hrj :=
    s.velocity_firstPartial_spatialC1
      ht j r

  have hlr :=
    s.velocity_firstPartial_spatialC1
      ht r l

  have hkrj :=
    velocitySecondPartial_spatialC1_orderThreeExpansion
      s ht j k r

  have hkr :=
    s.velocity_firstPartial_spatialC1
      ht r k

  have hrlj :=
    velocitySecondPartial_spatialC1_orderThreeExpansion
      s ht j r l

  unfold secondTransportCommutatorAxisBlock

  exact
    (hklr.mul hrj)
      |>.add (hlr.mul hkrj)
      |>.add (hkr.mul hrlj)

noncomputable def secondTransportCommutatorAxisDerivativeBlock
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j r : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    (
      spatial3.d i
        (spatial3.d k
          (spatial3.d l
            (fun q => (v t q).component r))) x
        *
      spatial3.d r
        (fun q => (v t q).component j) x
    )
      +
    (
      spatial3.d k
        (spatial3.d l
          (fun q => (v t q).component r)) x
        *
      spatial3.d i
        (spatial3.d r
          (fun q => (v t q).component j)) x
    )
      +
    (
      spatial3.d i
        (spatial3.d l
          (fun q => (v t q).component r)) x
        *
      spatial3.d k
        (spatial3.d r
          (fun q => (v t q).component j)) x
    )
      +
    (
      spatial3.d l
        (fun q => (v t q).component r) x
        *
      spatial3.d i
        (spatial3.d k
          (spatial3.d r
            (fun q => (v t q).component j))) x
    )
      +
    (
      spatial3.d i
        (spatial3.d k
          (fun q => (v t q).component r)) x
        *
      spatial3.d r
        (spatial3.d l
          (fun q => (v t q).component j)) x
    )
      +
    (
      spatial3.d k
        (fun q => (v t q).component r) x
        *
      spatial3.d i
        (spatial3.d r
          (spatial3.d l
            (fun q => (v t q).component j))) x
    )

theorem spatial_d_secondTransportCommutatorAxisBlock
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
    (x : Point3)
    (i k l j r : PrimeTensor.Axis Depth.three) :
    spatial3.d
        i
        (
          secondTransportCommutatorAxisBlock
            v t k l j r
        )
        x
      =
    secondTransportCommutatorAxisDerivativeBlock
        v t i k l j r x := by

  have hklr :=
    velocitySecondPartial_spatialC1_orderThreeExpansion
      s ht r k l

  have hrj :=
    s.velocity_firstPartial_spatialC1
      ht j r

  have hlr :=
    s.velocity_firstPartial_spatialC1
      ht r l

  have hkrj :=
    velocitySecondPartial_spatialC1_orderThreeExpansion
      s ht j k r

  have hkr :=
    s.velocity_firstPartial_spatialC1
      ht r k

  have hrlj :=
    velocitySecondPartial_spatialC1_orderThreeExpansion
      s ht j r l

  have hp1 := hklr.mul hrj
  have hp2 := hlr.mul hkrj
  have hp3 := hkr.mul hrlj

  unfold secondTransportCommutatorAxisBlock

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      (hp1.add hp2) hp3 x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hp1 hp2 x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hklr hrj x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hlr hkrj x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hkr hrlj x i
  ]

  unfold secondTransportCommutatorAxisDerivativeBlock

  ring

theorem spatial_d_secondTransportCommutatorExpanded
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
    (x : Point3)
    (i k l j : PrimeTensor.Axis Depth.three) :
    spatial3.d
        i
        (
          secondTransportCommutatorExpanded
            v t k l j
        )
        x
      =
    secondTransportCommutatorAxisDerivativeBlock
        v t i k l j xAxis x
      +
    (
      secondTransportCommutatorAxisDerivativeBlock
          v t i k l j yAxis x
        +
      secondTransportCommutatorAxisDerivativeBlock
          v t i k l j zAxis x
    ) := by

  have hx :=
    secondTransportCommutatorAxisBlock_spatialC1
      s ht k l j xAxis

  have hy :=
    secondTransportCommutatorAxisBlock_spatialC1
      s ht k l j yAxis

  have hz :=
    secondTransportCommutatorAxisBlock_spatialC1
      s ht k l j zAxis

  have hyz :=
    hy.add hz

  have hField :
      secondTransportCommutatorExpanded
          v t k l j
        =
      fun q =>
        secondTransportCommutatorAxisBlock
            v t k l j xAxis q
          +
        (
          secondTransportCommutatorAxisBlock
              v t k l j yAxis q
            +
          secondTransportCommutatorAxisBlock
              v t k l j zAxis q
        ) := by

    funext q

    exact
      secondTransportCommutatorExpanded_eq_axisBlocks
        t q k l j

  have hDeriv :=
    congrFun
      (
        congrArg
          (spatial3.d i)
          hField
      )
      x

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hx hyz x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hy hz x i,
    spatial_d_secondTransportCommutatorAxisBlock
      s ht x i k l j xAxis,
    spatial_d_secondTransportCommutatorAxisBlock
      s ht x i k l j yAxis,
    spatial_d_secondTransportCommutatorAxisBlock
      s ht x i k l j zAxis
  ] at hDeriv

  exact hDeriv

noncomputable def thirdTransportCommutatorAxisBlock
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j r : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    secondTransportCommutatorAxisDerivativeBlock
        v t i k l j r x
      +
    (
      spatial3.d i
        (fun q => (v t q).component r) x
        *
      spatial3.d r
        (spatial3.d k
          (spatial3.d l
            (fun q => (v t q).component j))) x
    )

noncomputable def thirdTransportCommutatorExpanded
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    thirdTransportCommutatorAxisBlock
        v t i k l j xAxis x
      +
    (
      thirdTransportCommutatorAxisBlock
          v t i k l j yAxis x
        +
      thirdTransportCommutatorAxisBlock
          v t i k l j zAxis x
    )

theorem thirdTransportCommutator_eq_expanded
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
    (x : Point3)
    (i k l j : PrimeTensor.Axis Depth.three) :
    thirdTransportCommutator
        v t i k l j x
      =
    thirdTransportCommutatorExpanded
        v t i k l j x := by

  have hC2 :
      secondTransportCommutator
          v t k l j
        =
      secondTransportCommutatorExpanded
          v t k l j := by

    funext q

    exact
      secondTransportCommutator_eq_expanded
        s ht q k l j

  unfold thirdTransportCommutator

  rw [hC2]

  rw [
    spatial_d_secondTransportCommutatorExpanded
      s ht x i k l j
  ]

  unfold
    scalarTransportDerivativeCommutator
    thirdTransportCommutatorExpanded
    thirdTransportCommutatorAxisBlock
    secondTransportCommutatorAxisDerivativeBlock

  ring

end Euclidean
end Bridge
end PrimeTensor
