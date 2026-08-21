import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Expansion
import PrimeTensor.Fluid.Vorticity.H3.Energy.Regularity

/-!
# Third-order transport regularity from the H³ energy class

`H3OrderThreeTransportRegularityAt` was previously carried as an independent
Landau-tail hypothesis.  It is in fact local regularity already contained in
`PreterminalH3EnergyClass`.

The first conjunct, `SpatialC1` regularity of the order-two transport
commutator, follows from the ordinary preterminal spatial `C³` regularity after
expanding the commutator into its coordinate blocks.

The second conjunct, `SpatialC2` regularity of every transported second
velocity derivative, follows immediately from the stronger `VelocitySpatialC5OnTail`
field of the H³ energy class.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

noncomputable local instance axisFintypeH3OrderThreeRegularityClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

private theorem velocitySecondPartial_spatialC1_orderThreeRegularity
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

private theorem secondTransportCommutatorAxisBlock_spatialC1_orderThreeRegularity
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
    velocitySecondPartial_spatialC1_orderThreeRegularity
      s ht r k l

  have hrj :=
    s.velocity_firstPartial_spatialC1
      ht j r

  have hlr :=
    s.velocity_firstPartial_spatialC1
      ht r l

  have hkrj :=
    velocitySecondPartial_spatialC1_orderThreeRegularity
      s ht j k r

  have hkr :=
    s.velocity_firstPartial_spatialC1
      ht r k

  have hrlj :=
    velocitySecondPartial_spatialC1_orderThreeRegularity
      s ht j r l

  unfold secondTransportCommutatorAxisBlock

  exact
    (hklr.mul hrj)
      |>.add (hlr.mul hkrj)
      |>.add (hkr.mul hrlj)

private theorem secondTransportCommutator_spatialC1_orderThreeRegularity
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
    (k l j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        secondTransportCommutator
          v t k l j
      ) := by

  have hx :
      SpatialC1
        (
          secondTransportCommutatorAxisBlock
            v t k l j xAxis
        ) :=
    secondTransportCommutatorAxisBlock_spatialC1_orderThreeRegularity
      s ht k l j xAxis

  have hy :
      SpatialC1
        (
          secondTransportCommutatorAxisBlock
            v t k l j yAxis
        ) :=
    secondTransportCommutatorAxisBlock_spatialC1_orderThreeRegularity
      s ht k l j yAxis

  have hz :
      SpatialC1
        (
          secondTransportCommutatorAxisBlock
            v t k l j zAxis
        ) :=
    secondTransportCommutatorAxisBlock_spatialC1_orderThreeRegularity
      s ht k l j zAxis

  have hExpanded :
      SpatialC1
        (
          secondTransportCommutatorExpanded
            v t k l j
        ) := by

    have hSum :
        SpatialC1
          (
            fun x =>
              secondTransportCommutatorAxisBlock
                  v t k l j xAxis x
                +
              (
                secondTransportCommutatorAxisBlock
                    v t k l j yAxis x
                  +
                secondTransportCommutatorAxisBlock
                    v t k l j zAxis x
              )
          ) :=
      hx.add (hy.add hz)

    have hEq :
        secondTransportCommutatorExpanded
            v t k l j
          =
        fun x =>
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

      funext x

      exact
        secondTransportCommutatorExpanded_eq_axisBlocks
          t x k l j

    rw [hEq]

    exact hSum

  have hEq :
      secondTransportCommutator
          v t k l j
        =
      secondTransportCommutatorExpanded
          v t k l j := by

    funext x

    exact
      secondTransportCommutator_eq_expanded
        s ht x k l j

  rw [hEq]

  exact hExpanded

/--
The top-order local transport regularity package is automatic inside the H³
energy class.
-/
theorem h3OrderThreeTransportRegularityAt_of_energyClass
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
    ) :
    H3OrderThreeTransportRegularityAt
      u t := by

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

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨
      le_of_lt ht.1,
      ht.2
    ⟩

  intro k l j

  constructor

  · exact
      secondTransportCommutator_spatialC1_orderThreeRegularity
        s htNS k l j

  · have h3 :
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
          ) := by

      simpa using
        hClass.velocity_spatial_five
          t htTail j k l

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.toSpatialC2
        h3

end Euclidean
end Bridge
end PrimeTensor
