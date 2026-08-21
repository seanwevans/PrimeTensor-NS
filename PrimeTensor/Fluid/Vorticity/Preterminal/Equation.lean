import PrimeTensor.Fluid.Vorticity.Preterminal.Extension
import PrimeTensor.Bridge.Euclidean.Vorticity.Equation
import PrimeTensor.Bridge.Euclidean.Vorticity.Native

/-!
# Vorticity equation on a preterminal Navier--Stokes interval

The existing classical curl derivation is packaged for `VorticitySolution3`,
whose PDE and regularity hypotheses hold for every real time.  A continuation
argument cannot use that global object at a candidate first singular time.

This file ports exactly the local ingredients of the curl calculation to
`PreterminalNavierStokes3 v p T`.  Every PDE or spacetime-regularity hypothesis
is consumed only at a time `t ∈ (0,T)`.

The final theorem crosses the already-proved logarithmic/native bridge once:

    LoggedPreterminalNavierStokesAdmissible u T
      -> t ∈ (0,T)
      -> MulVorticityBalance3 u t x.

Thus stagewise native vorticity balance is no longer an independent hypothesis
for a strictly preterminal refinement path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable local instance axisFintypePreterminalVorticity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

namespace PreterminalNavierStokes3

/-- Expanded incompressibility at a preterminal time. -/
theorem incompressible_xyz
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
          xAxis
          (fun y =>
            (v t y).component xAxis)
          x
      +
        (
          spatial3.d
              yAxis
              (fun y =>
                (v t y).component yAxis)
              x
          +
          spatial3.d
              zAxis
              (fun y =>
                (v t y).component zAxis)
              x
        )
      =
    0 := by

  have h :=
    s.incompressible t ht x

  unfold
    PrimeTensor.Bridge.RealFluid.divergence
    at h

  rw [
    PrimeTensor.Bridge.Euclidean.axis_fold_three
  ] at h

  exact h

/-- Expanded normalized momentum equation at a preterminal time. -/
theorem momentum_xyz
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    temporal.d
          (fun τ =>
            (v τ x).component j)
          t
      +
        (
          (v t x).component xAxis *
              spatial3.d
                xAxis
                (fun y =>
                  (v t y).component j)
                x
          +
          (
            (v t x).component yAxis *
                spatial3.d
                  yAxis
                  (fun y =>
                    (v t y).component j)
                  x
            +
            (v t x).component zAxis *
                spatial3.d
                  zAxis
                  (fun y =>
                    (v t y).component j)
                  x
          )
        )
      =
    -
        spatial3.d
          j
          (p t)
          x
      +
        (
          spatial3.d
              xAxis
              (
                spatial3.d
                  xAxis
                  (fun y =>
                    (v t y).component j)
              )
              x
          +
          (
            spatial3.d
                yAxis
                (
                  spatial3.d
                    yAxis
                    (fun y =>
                      (v t y).component j)
                )
                x
            +
            spatial3.d
                zAxis
                (
                  spatial3.d
                    zAxis
                    (fun y =>
                      (v t y).component j)
                )
                x
          )
        ) := by

  have h :=
    s.momentum t ht x j

  change
    temporal.d
          (fun τ =>
            (v τ x).component j)
          t
      +
        PrimeTensor.Axis.fold
          (· + ·)
          Depth.three
          (fun i =>
            (v t x).component i *
              spatial3.d
                i
                (fun y =>
                  (v t y).component j)
                x)
      =
    -
        spatial3.d
          j
          (p t)
          x
      +
        PrimeTensor.Axis.fold
          (· + ·)
          Depth.three
          (fun i =>
            spatial3.d
              i
              (
                spatial3.d
                  i
                  (fun y =>
                    (v t y).component j)
              )
              x)
    at h

  rw [
    PrimeTensor.Bridge.Euclidean.axis_fold_three,
    PrimeTensor.Bridge.Euclidean.axis_fold_three
  ] at h

  exact h

/-- Every fixed-time velocity component is spatially `C¹`. -/
theorem velocity_component_spatialC1
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        fun y =>
          (v t y).component j
      ) := by

  have h3 :=
    s.regularity.velocity_spatial_three
      t ht j

  unfold SpatialC3 at h3
  unfold SpatialC1

  exact
    h3.of_le
      (by norm_num)

/-- Every first spatial partial of a velocity component is spatially `C¹`. -/
theorem velocity_firstPartial_spatialC1
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j i : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        spatial3.d
          i
          (
            fun y =>
              (v t y).component j
          )
      ) := by

  have h3 :
      SpatialC3
        (
          fun y =>
            (v t y).component j
        ) :=
    s.regularity.velocity_spatial_three
      t ht j

  have h2 :
      SpatialC2
        (
          fun y =>
            partialDeriv i
              (
                fun q =>
                  (v t q).component j
              )
              y
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      h3 i

  change
    SpatialC1
      (
        fun y =>
          partialDeriv i
            (
              fun q =>
                (v t q).component j
            )
            y
      )

  exact
    h2.of_le
      (by norm_num)

/-- Mixed spatial partials of every velocity component commute preterminally. -/
theorem velocity_spatial_d_comm
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (k i j : PrimeTensor.Axis Depth.three) :
    spatial3.d i
        (
          spatial3.d j
            (
              fun y =>
                (v t y).component k
            )
        )
        x
      =
    spatial3.d j
        (
          spatial3.d i
            (
              fun y =>
                (v t y).component k
            )
        )
        x := by

  have h3 :=
    s.regularity.velocity_spatial_three
      t ht k

  have h2 :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.toSpatialC2
      h3

  exact
    h2.spatial_d_comm
      x i j

/-- A fixed-time advection component is spatially `C¹`. -/
theorem realAdvectionComponent_spatialC1
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        fun x =>
          realAdvectionComponent
            v t x j
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

  have hdx :=
    s.velocity_firstPartial_spatialC1
      ht j xAxis

  have hdy :=
    s.velocity_firstPartial_spatialC1
      ht j yAxis

  have hdz :=
    s.velocity_firstPartial_spatialC1
      ht j zAxis

  unfold realAdvectionComponent

  exact
    (hux.mul hdx).add
      (
        (huy.mul hdy).add
          (huz.mul hdz)
      )

/-- One spatial derivative of the advection component, expanded by product rule. -/
theorem spatial_d_realAdvectionComponent
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (
          fun q =>
            realAdvectionComponent
              v t q j
        )
        x
      =
    (
      spatial3.d
          a
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
      (v t x).component xAxis
        *
      spatial3.d
          a
          (
            spatial3.d
              xAxis
              (
                fun q =>
                  (v t q).component j
              )
          )
          x
    )
      +
    (
      (
        spatial3.d
            a
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
        (v t x).component yAxis
          *
        spatial3.d
            a
            (
              spatial3.d
                yAxis
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
            a
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
          +
        (v t x).component zAxis
          *
        spatial3.d
            a
            (
              spatial3.d
                zAxis
                (
                  fun q =>
                    (v t q).component j
                )
            )
            x
      )
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

  have hdx :=
    s.velocity_firstPartial_spatialC1
      ht j xAxis

  have hdy :=
    s.velocity_firstPartial_spatialC1
      ht j yAxis

  have hdz :=
    s.velocity_firstPartial_spatialC1
      ht j zAxis

  have hpx :
      SpatialC1
        (
          fun q =>
            (v t q).component xAxis
              *
            spatial3.d
              xAxis
              (
                fun y =>
                  (v t y).component j
              )
              q
        ) :=
    hux.mul hdx

  have hpy :
      SpatialC1
        (
          fun q =>
            (v t q).component yAxis
              *
            spatial3.d
              yAxis
              (
                fun y =>
                  (v t y).component j
              )
              q
        ) :=
    huy.mul hdy

  have hpz :
      SpatialC1
        (
          fun q =>
            (v t q).component zAxis
              *
            spatial3.d
              zAxis
              (
                fun y =>
                  (v t y).component j
              )
              q
        ) :=
    huz.mul hdz

  have hpyz :
      SpatialC1
        (
          fun q =>
            (
              (v t q).component yAxis
                *
              spatial3.d
                yAxis
                (
                  fun y =>
                    (v t y).component j
                )
                q
            )
              +
            (
              (v t q).component zAxis
                *
              spatial3.d
                zAxis
                (
                  fun y =>
                    (v t y).component j
                )
                q
            )
        ) :=
    hpy.add hpz

  unfold realAdvectionComponent

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hpx hpyz x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hux hdx x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hpy hpz x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      huy hdy x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      huz hdz x a
  ]

/-- Explicit divergence vanishes at every preterminal time. -/
theorem realDivergence3_eq_zero
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    realDivergence3 v t x = 0 := by

  unfold realDivergence3

  exact
    s.incompressible_xyz
      ht x

/-- Coordinate derivative of x-vorticity. -/
theorem spatial_d_realVorticityX
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (fun q =>
          realVorticityX v t q)
        x
      =
    spatial3.d
        a
        (
          spatial3.d
            yAxis
            (fun q =>
              (v t q).component zAxis)
        )
        x
      -
    spatial3.d
        a
        (
          spatial3.d
            zAxis
            (fun q =>
              (v t q).component yAxis)
        )
        x := by

  have hy :=
    s.velocity_firstPartial_spatialC1
      ht zAxis yAxis

  have hz :=
    s.velocity_firstPartial_spatialC1
      ht yAxis zAxis

  unfold realVorticityX

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hy hz x a

/-- Coordinate derivative of y-vorticity. -/
theorem spatial_d_realVorticityY
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (fun q =>
          realVorticityY v t q)
        x
      =
    spatial3.d
        a
        (
          spatial3.d
            zAxis
            (fun q =>
              (v t q).component xAxis)
        )
        x
      -
    spatial3.d
        a
        (
          spatial3.d
            xAxis
            (fun q =>
              (v t q).component zAxis)
        )
        x := by

  have hz :=
    s.velocity_firstPartial_spatialC1
      ht xAxis zAxis

  have hx :=
    s.velocity_firstPartial_spatialC1
      ht zAxis xAxis

  unfold realVorticityY

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hz hx x a

/-- Coordinate derivative of z-vorticity. -/
theorem spatial_d_realVorticityZ
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (fun q =>
          realVorticityZ v t q)
        x
      =
    spatial3.d
        a
        (
          spatial3.d
            xAxis
            (fun q =>
              (v t q).component yAxis)
        )
        x
      -
    spatial3.d
        a
        (
          spatial3.d
            yAxis
            (fun q =>
              (v t q).component xAxis)
        )
        x := by

  have hx :=
    s.velocity_firstPartial_spatialC1
      ht yAxis xAxis

  have hy :=
    s.velocity_firstPartial_spatialC1
      ht xAxis yAxis

  unfold realVorticityZ

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hx hy x a

/-- Curl of advection, x-component, before imposing incompressibility. -/
theorem curlAdvectionX_with_divergence
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        yAxis
        (fun q =>
          realAdvectionComponent
            v t q zAxis)
        x
      -
    spatial3.d
        zAxis
        (fun q =>
          realAdvectionComponent
            v t q yAxis)
        x
      =
    realVorticityTransportX
        v t x
      -
    realVortexStretchComponent
        v t x xAxis
      +
    realDivergence3
        v t x
      *
    realVorticityX
        v t x := by

  rw [
    s.spatial_d_realAdvectionComponent
      ht x yAxis zAxis,
    s.spatial_d_realAdvectionComponent
      ht x zAxis yAxis
  ]

  unfold
    realVorticityTransportX
    realVortexStretchComponent
    realDivergence3

  rw [
    s.spatial_d_realVorticityX
      ht x xAxis,
    s.spatial_d_realVorticityX
      ht x yAxis,
    s.spatial_d_realVorticityX
      ht x zAxis
  ]

  rw [
    s.velocity_spatial_d_comm
      ht x zAxis yAxis xAxis,
    s.velocity_spatial_d_comm
      ht x yAxis zAxis xAxis,
    s.velocity_spatial_d_comm
      ht x zAxis yAxis zAxis,
    s.velocity_spatial_d_comm
      ht x yAxis zAxis yAxis
  ]

  unfold
    realVorticityX
    realVorticityY
    realVorticityZ

  ring

/-- Curl of advection, y-component, before imposing incompressibility. -/
theorem curlAdvectionY_with_divergence
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        zAxis
        (fun q =>
          realAdvectionComponent
            v t q xAxis)
        x
      -
    spatial3.d
        xAxis
        (fun q =>
          realAdvectionComponent
            v t q zAxis)
        x
      =
    realVorticityTransportY
        v t x
      -
    realVortexStretchComponent
        v t x yAxis
      +
    realDivergence3
        v t x
      *
    realVorticityY
        v t x := by

  rw [
    s.spatial_d_realAdvectionComponent
      ht x zAxis xAxis,
    s.spatial_d_realAdvectionComponent
      ht x xAxis zAxis
  ]

  unfold
    realVorticityTransportY
    realVortexStretchComponent
    realDivergence3

  rw [
    s.spatial_d_realVorticityY
      ht x xAxis,
    s.spatial_d_realVorticityY
      ht x yAxis,
    s.spatial_d_realVorticityY
      ht x zAxis
  ]

  rw [
    s.velocity_spatial_d_comm
      ht x xAxis zAxis xAxis,
    s.velocity_spatial_d_comm
      ht x xAxis zAxis yAxis,
    s.velocity_spatial_d_comm
      ht x zAxis xAxis yAxis,
    s.velocity_spatial_d_comm
      ht x zAxis xAxis zAxis
  ]

  unfold
    realVorticityX
    realVorticityY
    realVorticityZ

  ring

/-- Curl of advection, z-component, before imposing incompressibility. -/
theorem curlAdvectionZ_with_divergence
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        xAxis
        (fun q =>
          realAdvectionComponent
            v t q yAxis)
        x
      -
    spatial3.d
        yAxis
        (fun q =>
          realAdvectionComponent
            v t q xAxis)
        x
      =
    realVorticityTransportZ
        v t x
      -
    realVortexStretchComponent
        v t x zAxis
      +
    realDivergence3
        v t x
      *
    realVorticityZ
        v t x := by

  rw [
    s.spatial_d_realAdvectionComponent
      ht x xAxis yAxis,
    s.spatial_d_realAdvectionComponent
      ht x yAxis xAxis
  ]

  unfold
    realVorticityTransportZ
    realVortexStretchComponent
    realDivergence3

  rw [
    s.spatial_d_realVorticityZ
      ht x xAxis,
    s.spatial_d_realVorticityZ
      ht x yAxis,
    s.spatial_d_realVorticityZ
      ht x zAxis
  ]

  rw [
    s.velocity_spatial_d_comm
      ht x yAxis xAxis yAxis,
    s.velocity_spatial_d_comm
      ht x yAxis xAxis zAxis,
    s.velocity_spatial_d_comm
      ht x xAxis yAxis xAxis,
    s.velocity_spatial_d_comm
      ht x xAxis yAxis zAxis
  ]

  unfold
    realVorticityX
    realVorticityY
    realVorticityZ

  ring

/-- Incompressible x-component curl-advection identity. -/
theorem curlAdvectionX_eq_transport_sub_stretch
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        yAxis
        (fun q =>
          realAdvectionComponent
            v t q zAxis)
        x
      -
    spatial3.d
        zAxis
        (fun q =>
          realAdvectionComponent
            v t q yAxis)
        x
      =
    realVorticityTransportX
        v t x
      -
    realVortexStretchComponent
        v t x xAxis := by

  calc
    spatial3.d
          yAxis
          (fun q =>
            realAdvectionComponent
              v t q zAxis)
          x
        -
      spatial3.d
          zAxis
          (fun q =>
            realAdvectionComponent
              v t q yAxis)
          x
      =
      realVorticityTransportX v t x
        -
      realVortexStretchComponent v t x xAxis
        +
      realDivergence3 v t x
        *
      realVorticityX v t x :=
      s.curlAdvectionX_with_divergence
        ht x

    _ =
      realVorticityTransportX v t x
        -
      realVortexStretchComponent v t x xAxis := by
      rw [s.realDivergence3_eq_zero ht x]
      ring

/-- Incompressible y-component curl-advection identity. -/
theorem curlAdvectionY_eq_transport_sub_stretch
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        zAxis
        (fun q =>
          realAdvectionComponent
            v t q xAxis)
        x
      -
    spatial3.d
        xAxis
        (fun q =>
          realAdvectionComponent
            v t q zAxis)
        x
      =
    realVorticityTransportY
        v t x
      -
    realVortexStretchComponent
        v t x yAxis := by

  calc
    spatial3.d
          zAxis
          (fun q =>
            realAdvectionComponent
              v t q xAxis)
          x
        -
      spatial3.d
          xAxis
          (fun q =>
            realAdvectionComponent
              v t q zAxis)
          x
      =
      realVorticityTransportY v t x
        -
      realVortexStretchComponent v t x yAxis
        +
      realDivergence3 v t x
        *
      realVorticityY v t x :=
      s.curlAdvectionY_with_divergence
        ht x

    _ =
      realVorticityTransportY v t x
        -
      realVortexStretchComponent v t x yAxis := by
      rw [s.realDivergence3_eq_zero ht x]
      ring

/-- Incompressible z-component curl-advection identity. -/
theorem curlAdvectionZ_eq_transport_sub_stretch
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        xAxis
        (fun q =>
          realAdvectionComponent
            v t q yAxis)
        x
      -
    spatial3.d
        yAxis
        (fun q =>
          realAdvectionComponent
            v t q xAxis)
        x
      =
    realVorticityTransportZ
        v t x
      -
    realVortexStretchComponent
        v t x zAxis := by

  calc
    spatial3.d
          xAxis
          (fun q =>
            realAdvectionComponent
              v t q yAxis)
          x
        -
      spatial3.d
          yAxis
          (fun q =>
            realAdvectionComponent
              v t q xAxis)
          x
      =
      realVorticityTransportZ v t x
        -
      realVortexStretchComponent v t x zAxis
        +
      realDivergence3 v t x
        *
      realVorticityZ v t x :=
      s.curlAdvectionZ_with_divergence
        ht x

    _ =
      realVorticityTransportZ v t x
        -
      realVortexStretchComponent v t x zAxis := by
      rw [s.realDivergence3_eq_zero ht x]
      ring

/-- Time differentiation commutes with x-vorticity at a preterminal time. -/
theorem temporal_realVorticityX
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityX v τ x)
        t
      =
    spatial3.d
        yAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (v τ y).component zAxis
              )
              t
        )
        x
      -
    spatial3.d
        zAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (v τ y).component yAxis
              )
              t
        )
        x := by

  have hy :=
    s.regularity.velocity_space_time_hasDerivAt
      t ht x yAxis zAxis

  have hz :=
    s.regularity.velocity_space_time_hasDerivAt
      t ht x zAxis yAxis

  have hsub :=
    hy.sub hz

  unfold temporal

  change
    deriv
        (
          fun τ =>
            spatial3.d
                yAxis
                (
                  fun y =>
                    (v τ y).component zAxis
                )
                x
              -
            spatial3.d
                zAxis
                (
                  fun y =>
                    (v τ y).component yAxis
                )
                x
        )
        t
      =
    spatial3.d
        yAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (v τ y).component zAxis
              )
              t
        )
        x
      -
    spatial3.d
        zAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (v τ y).component yAxis
              )
              t
        )
        x

  exact hsub.deriv

/-- Time differentiation commutes with y-vorticity at a preterminal time. -/
theorem temporal_realVorticityY
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityY v τ x)
        t
      =
    spatial3.d
        zAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (v τ y).component xAxis
              )
              t
        )
        x
      -
    spatial3.d
        xAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (v τ y).component zAxis
              )
              t
        )
        x := by

  have hz :=
    s.regularity.velocity_space_time_hasDerivAt
      t ht x zAxis xAxis

  have hx :=
    s.regularity.velocity_space_time_hasDerivAt
      t ht x xAxis zAxis

  have hsub :=
    hz.sub hx

  unfold temporal

  change
    deriv
        (
          fun τ =>
            spatial3.d
                zAxis
                (
                  fun y =>
                    (v τ y).component xAxis
                )
                x
              -
            spatial3.d
                xAxis
                (
                  fun y =>
                    (v τ y).component zAxis
                )
                x
        )
        t
      =
    spatial3.d
        zAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (v τ y).component xAxis
              )
              t
        )
        x
      -
    spatial3.d
        xAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (v τ y).component zAxis
              )
              t
        )
        x

  exact hsub.deriv

/-- Time differentiation commutes with z-vorticity at a preterminal time. -/
theorem temporal_realVorticityZ
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityZ v τ x)
        t
      =
    spatial3.d
        xAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (v τ y).component yAxis
              )
              t
        )
        x
      -
    spatial3.d
        yAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (v τ y).component xAxis
              )
              t
        )
        x := by

  have hx :=
    s.regularity.velocity_space_time_hasDerivAt
      t ht x xAxis yAxis

  have hy :=
    s.regularity.velocity_space_time_hasDerivAt
      t ht x yAxis xAxis

  have hsub :=
    hx.sub hy

  unfold temporal

  change
    deriv
        (
          fun τ =>
            spatial3.d
                xAxis
                (
                  fun y =>
                    (v τ y).component yAxis
                )
                x
              -
            spatial3.d
                yAxis
                (
                  fun y =>
                    (v τ y).component xAxis
                )
                x
        )
        t
      =
    spatial3.d
        xAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (v τ y).component yAxis
              )
              t
        )
        x
      -
    spatial3.d
        yAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (v τ y).component xAxis
              )
              t
        )
        x

  exact hsub.deriv

/-- x-component of curl(grad p) vanishes preterminally. -/
theorem pressureCurlX_eq_zero
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        yAxis
        (
          spatial3.d
            zAxis
            (p t)
        )
        x
      -
    spatial3.d
        zAxis
        (
          spatial3.d
            yAxis
            (p t)
        )
        x
      =
    0 := by

  have h :=
    (
      s.regularity.pressure_spatial_two
        t ht
    ).spatial_d_comm
      x yAxis zAxis

  have h3 :
      spatial3.d
          yAxis
          (spatial3.d zAxis (p t))
          x
        =
      spatial3.d
          zAxis
          (spatial3.d yAxis (p t))
          x := by
    simpa only [spatial3] using h

  rw [h3]
  ring

/-- y-component of curl(grad p) vanishes preterminally. -/
theorem pressureCurlY_eq_zero
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        zAxis
        (
          spatial3.d
            xAxis
            (p t)
        )
        x
      -
    spatial3.d
        xAxis
        (
          spatial3.d
            zAxis
            (p t)
        )
        x
      =
    0 := by

  have h :=
    (
      s.regularity.pressure_spatial_two
        t ht
    ).spatial_d_comm
      x zAxis xAxis

  have h3 :
      spatial3.d
          zAxis
          (spatial3.d xAxis (p t))
          x
        =
      spatial3.d
          xAxis
          (spatial3.d zAxis (p t))
          x := by
    simpa only [spatial3] using h

  rw [h3]
  ring

/-- z-component of curl(grad p) vanishes preterminally. -/
theorem pressureCurlZ_eq_zero
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        xAxis
        (
          spatial3.d
            yAxis
            (p t)
        )
        x
      -
    spatial3.d
        yAxis
        (
          spatial3.d
            xAxis
            (p t)
        )
        x
      =
    0 := by

  have h :=
    (
      s.regularity.pressure_spatial_two
        t ht
    ).spatial_d_comm
      x xAxis yAxis

  have h3 :
      spatial3.d
          xAxis
          (spatial3.d yAxis (p t))
          x
        =
      spatial3.d
          yAxis
          (spatial3.d xAxis (p t))
          x := by
    simpa only [spatial3] using h

  rw [h3]
  ring

/-- x-component of curl commutes with the Laplacian preterminally. -/
theorem curlLaplacianX_eq_laplacianVorticityX
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        yAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (v t y).component zAxis
            )
        )
        x
      -
    spatial3.d
        zAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (v t y).component yAxis
            )
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          realVorticityX v t y
      )
      x := by

  let uz : ScalarField3 :=
    fun y =>
      (v t y).component zAxis

  let uy : ScalarField3 :=
    fun y =>
      (v t y).component yAxis

  have huz3 : SpatialC3 uz := by
    simpa [uz] using
      s.regularity.velocity_spatial_three
        t ht zAxis

  have huy3 : SpatialC3 uy := by
    simpa [uy] using
      s.regularity.velocity_spatial_three
        t ht yAxis

  change
    spatial3.d
        yAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uz
        )
        x
      -
    spatial3.d
        zAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uy
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          spatial3.d yAxis uz y
            -
          spatial3.d zAxis uy y
      )
      x

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.curlLaplacianPair
      huz3 huy3 x yAxis zAxis

/-- y-component of curl commutes with the Laplacian preterminally. -/
theorem curlLaplacianY_eq_laplacianVorticityY
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        zAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (v t y).component xAxis
            )
        )
        x
      -
    spatial3.d
        xAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (v t y).component zAxis
            )
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          realVorticityY v t y
      )
      x := by

  let ux : ScalarField3 :=
    fun y =>
      (v t y).component xAxis

  let uz : ScalarField3 :=
    fun y =>
      (v t y).component zAxis

  have hux3 : SpatialC3 ux := by
    simpa [ux] using
      s.regularity.velocity_spatial_three
        t ht xAxis

  have huz3 : SpatialC3 uz := by
    simpa [uz] using
      s.regularity.velocity_spatial_three
        t ht zAxis

  change
    spatial3.d
        zAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 ux
        )
        x
      -
    spatial3.d
        xAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uz
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          spatial3.d zAxis ux y
            -
          spatial3.d xAxis uz y
      )
      x

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.curlLaplacianPair
      hux3 huz3 x zAxis xAxis

/-- z-component of curl commutes with the Laplacian preterminally. -/
theorem curlLaplacianZ_eq_laplacianVorticityZ
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    spatial3.d
        xAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (v t y).component yAxis
            )
        )
        x
      -
    spatial3.d
        yAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (v t y).component xAxis
            )
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          realVorticityZ v t y
      )
      x := by

  let uy : ScalarField3 :=
    fun y =>
      (v t y).component yAxis

  let ux : ScalarField3 :=
    fun y =>
      (v t y).component xAxis

  have huy3 : SpatialC3 uy := by
    simpa [uy] using
      s.regularity.velocity_spatial_three
        t ht yAxis

  have hux3 : SpatialC3 ux := by
    simpa [ux] using
      s.regularity.velocity_spatial_three
        t ht xAxis

  change
    spatial3.d
        xAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uy
        )
        x
      -
    spatial3.d
        yAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 ux
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          spatial3.d xAxis uy y
            -
          spatial3.d yAxis ux y
      )
      x

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.curlLaplacianPair
      huy3 hux3 x xAxis yAxis

/-- Momentum rearranged as temporal = Laplacian - advection - pressure. -/
theorem temporalComponent_eq_laplacian_sub_advection_sub_pressure
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    temporal.d
        (fun τ =>
          (v τ x).component j)
        t
      =
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          (v t y).component j)
        x
      -
    realAdvectionComponent
        v t x j
      -
    spatial3.d
        j
        (p t)
        x := by

  have h :=
    s.momentum_xyz
      ht x j

  rw [
    laplacian3_eq
  ]

  unfold realAdvectionComponent

  linarith

/--
A spatial derivative of the temporal component is computed from the spatially
regular right-hand side of the preterminal momentum equation.
-/
theorem spatial_d_temporalComponent
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (
          fun q =>
            temporal.d
              (fun τ =>
                (v τ q).component j)
              t
        )
        x
      =
    spatial3.d
        a
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (v t q).component j)
        )
        x
      -
    spatial3.d
        a
        (
          fun q =>
            realAdvectionComponent
              v t q j
        )
        x
      -
    spatial3.d
        a
        (
          spatial3.d
            j
            (p t)
        )
        x := by

  let uj : ScalarField3 :=
    fun q =>
      (v t q).component j

  have huj3 :
      SpatialC3 uj := by
    simpa [uj] using
      s.regularity.velocity_spatial_three
        t ht j

  have hlap :
      SpatialC1
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uj
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.laplacian3_spatialC1
      huj3

  have hadv :
      SpatialC1
        (
          fun q =>
            realAdvectionComponent
              v t q j
        ) :=
    s.realAdvectionComponent_spatialC1
      ht j

  have hp :
      SpatialC1
        (
          spatial3.d
            j
            (p t)
        ) := by

    have hp2 :=
      s.regularity.pressure_spatial_two
        t ht

    have h :=
      PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
        hp2 j

    change
      SpatialC1
        (
          fun y =>
            partialDeriv j (p t) y
        )

    exact h

  have hfun :
      (
        fun q =>
          temporal.d
            (fun τ =>
              (v τ q).component j)
            t
      )
        =
      (
        fun q =>
          PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uj q
            -
          realAdvectionComponent
              v t q j
            -
          spatial3.d
              j
              (p t)
              q
      ) := by

    funext q

    simpa [uj] using
      s.temporalComponent_eq_laplacian_sub_advection_sub_pressure
        ht q j

  rw [hfun]

  have hlapAdv :
      SpatialC1
        (
          fun q =>
            PrimeTensor.Bridge.RealFluid.laplacian
                spatial3 uj q
              -
            realAdvectionComponent
                v t q j
        ) :=
    hlap.sub hadv

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hlapAdv hp x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hlap hadv x a
  ]

/-- Preterminal x-component vorticity equation. -/
theorem vorticityEquationX
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityX v τ x)
        t
      +
    realVorticityTransportX
        v t x
      =
    realVortexStretchComponent
        v t x xAxis
      +
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityX v t y)
        x := by

  rw [
    s.temporal_realVorticityX
      ht x,
    s.spatial_d_temporalComponent
      ht x yAxis zAxis,
    s.spatial_d_temporalComponent
      ht x zAxis yAxis
  ]

  have hAdv :=
    s.curlAdvectionX_eq_transport_sub_stretch
      ht x

  have hPressure :=
    s.pressureCurlX_eq_zero
      ht x

  have hLaplacian :=
    s.curlLaplacianX_eq_laplacianVorticityX
      ht x

  linarith

/-- Preterminal y-component vorticity equation. -/
theorem vorticityEquationY
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityY v τ x)
        t
      +
    realVorticityTransportY
        v t x
      =
    realVortexStretchComponent
        v t x yAxis
      +
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityY v t y)
        x := by

  rw [
    s.temporal_realVorticityY
      ht x,
    s.spatial_d_temporalComponent
      ht x zAxis xAxis,
    s.spatial_d_temporalComponent
      ht x xAxis zAxis
  ]

  have hAdv :=
    s.curlAdvectionY_eq_transport_sub_stretch
      ht x

  have hPressure :=
    s.pressureCurlY_eq_zero
      ht x

  have hLaplacian :=
    s.curlLaplacianY_eq_laplacianVorticityY
      ht x

  linarith

/-- Preterminal z-component vorticity equation. -/
theorem vorticityEquationZ
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
    (s : PreterminalNavierStokes3 v p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityZ v τ x)
        t
      +
    realVorticityTransportZ
        v t x
      =
    realVortexStretchComponent
        v t x zAxis
      +
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityZ v t y)
        x := by

  rw [
    s.temporal_realVorticityZ
      ht x,
    s.spatial_d_temporalComponent
      ht x xAxis yAxis,
    s.spatial_d_temporalComponent
      ht x yAxis xAxis
  ]

  have hAdv :=
    s.curlAdvectionZ_eq_transport_sub_stretch
      ht x

  have hPressure :=
    s.pressureCurlZ_eq_zero
      ht x

  have hLaplacian :=
    s.curlLaplacianZ_eq_laplacianVorticityZ
      ht x

  linarith

end PreterminalNavierStokes3

/--
A logged preterminal Navier--Stokes solution satisfies the full intrinsic
multiplicative vorticity balance at every interior spacetime point.
-/
theorem mulVorticityBalance3_of_loggedPreterminalNavierStokes
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T t : ℝ}
    {x : Point3}
    (
      hAdmissible :
        LoggedPreterminalNavierStokesAdmissible
          u T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    ) :
    MulVorticityBalance3
      u t x := by

  obtain ⟨p, s⟩ :=
    hAdmissible

  apply
    (
      mulVorticityBalance3_iff_loggedEquations
        u t x
    ).2

  exact
    ⟨
      s.vorticityEquationX ht x,
      s.vorticityEquationY ht x,
      s.vorticityEquationZ ht x
    ⟩

/--
Along every time-refinement path which remains strictly before `T`, logged
preterminal Navier--Stokes admissibility supplies all three native stage
balances automatically.
-/
theorem mulVorticityBalance3_path_of_loggedPreterminalNavierStokes
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hAdmissible :
        LoggedPreterminalNavierStokesAdmissible
          u T
    )
    (
      hBefore :
        TimePathStrictlyBefore
          τ T
    ) :
    ∀ n : Depth,
      MulVorticityBalance3
        u (τ n) x := by

  intro n

  exact
    mulVorticityBalance3_of_loggedPreterminalNavierStokes
      hAdmissible
      (hBefore n)

end Euclidean
end Bridge
end PrimeTensor
