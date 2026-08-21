import PrimeTensor.Fluid.Vorticity.H3.Energy.Spatial.Linearity
import PrimeTensor.Fluid.Vorticity.H3.Energy.Regularity

/-!
# High-order energy class implies momentum-split regularity

This file connects `PreterminalH3EnergyClass` to the purely local regularity
package used by `VorticityH3EnergySpatialLinearity`.

The point is to discharge all derivative-linearity regularity from the
high-order energy class itself.

The proof is split into the three momentum pieces.

* Diffusion: the H5 witness says every second spatial partial of velocity is
  `SpatialC3`.  Hence the Laplacian is `SpatialC3`, so its first and second
  spatial derivatives have the `SpatialC1` regularity needed by the H3 split.
* Pressure: the C4 pressure witness is represented intrinsically by
  `SpatialC3 (∂ᵢ p)`.  One and two further spatial derivatives therefore have
  the required regularity.
* Transport: the existing first-derivative advection product formula is used
  directly.  The ordinary preterminal C3 regularity controls the undifferentiated
  and first-derivative factors, while the H5 witness controls the second
  derivatives.  This actually gives `SpatialC2` for the first derivative of
  advection, which is exactly enough to obtain `SpatialC1` after one more
  derivative.

No integration by parts, decay assumption, or estimate is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

noncomputable local instance axisFintypeH3EnergyClassSplitRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-! ## Small intrinsic regularity helpers -/

private theorem spatialC1_of_spatialC3
    {f : ScalarField3}
    (h : SpatialC3 f) :
    SpatialC1 f := by

  unfold SpatialC3 at h
  unfold SpatialC1

  exact
    h.of_le
      (by norm_num)

private theorem spatialC2_of_spatialC3
    {f : ScalarField3}
    (h : SpatialC3 f) :
    SpatialC2 f := by

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.toSpatialC2
      h

private theorem firstPartial_spatialC1_of_spatialC3
    {f : ScalarField3}
    (h : SpatialC3 f)
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (spatial3.d i f) := by

  have h2 :
      SpatialC2
        (
          fun y =>
            partialDeriv i f y
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      h i

  change
    SpatialC1
      (
        fun y =>
          partialDeriv i f y
      )

  exact
    h2.of_le
      (by norm_num)

private theorem firstPartial_spatialC2_of_spatialC3
    {f : ScalarField3}
    (h : SpatialC3 f)
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC2
      (spatial3.d i f) := by

  change
    SpatialC2
      (
        fun y =>
          partialDeriv i f y
      )

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      h i

private theorem secondPartial_spatialC1_of_spatialC3
    {f : ScalarField3}
    (h : SpatialC3 f)
    (i k : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        spatial3.d i
          (spatial3.d k f)
      ) := by

  have h2 :
      SpatialC2
        (spatial3.d k f) :=
    firstPartial_spatialC2_of_spatialC3
      h k

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      h2 i

/-! ## Diffusion -/

private theorem momentumDiffusion0Component_spatialC3_of_H5
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    (
      h5 :
        VelocitySpatialC5OnTail
          u a T
    )
    (
      ht :
        t ∈ Set.Ico a T
    )
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (
        momentumDiffusion0Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t j
      ) := by

  let f : ScalarField3 :=
    loggedVelocityComponent u t j

  have hxx :
      SpatialC3
        (
          spatial3.d xAxis
            (spatial3.d xAxis f)
        ) := by

    change
      SpatialC3
        (
          spatial3.d xAxis
            (
              spatial3.d xAxis
                (
                  fun x : Point3 =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t x
                    ).component j
                )
            )
        )

    exact
      h5 t ht j xAxis xAxis

  have hyy :
      SpatialC3
        (
          spatial3.d yAxis
            (spatial3.d yAxis f)
        ) := by

    change
      SpatialC3
        (
          spatial3.d yAxis
            (
              spatial3.d yAxis
                (
                  fun x : Point3 =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t x
                    ).component j
                )
            )
        )

    exact
      h5 t ht j yAxis yAxis

  have hzz :
      SpatialC3
        (
          spatial3.d zAxis
            (spatial3.d zAxis f)
        ) := by

    change
      SpatialC3
        (
          spatial3.d zAxis
            (
              spatial3.d zAxis
                (
                  fun x : Point3 =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t x
                    ).component j
                )
            )
        )

    exact
      h5 t ht j zAxis zAxis

  have hLap :
      momentumDiffusion0Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t j
        =
      fun x =>
        spatial3.d xAxis
            (spatial3.d xAxis f)
            x
          +
        (
          spatial3.d yAxis
              (spatial3.d yAxis f)
              x
            +
          spatial3.d zAxis
              (spatial3.d zAxis f)
              x
        ) := by

    funext x

    unfold momentumDiffusion0Component

    change
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 f x
        =
      spatial3.d xAxis
          (spatial3.d xAxis f)
          x
        +
      (
        spatial3.d yAxis
            (spatial3.d yAxis f)
            x
          +
        spatial3.d zAxis
            (spatial3.d zAxis f)
            x
      )

    exact
      laplacian3_eq f x

  rw [hLap]

  exact
    hxx.add
      (hyy.add hzz)

private theorem momentumDiffusion1Component_spatialC1_of_H5
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    (
      h5 :
        VelocitySpatialC5OnTail
          u a T
    )
    (
      ht :
        t ∈ Set.Ico a T
    )
    (k j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        momentumDiffusion1Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t k j
      ) := by

  unfold momentumDiffusion1Component

  exact
    firstPartial_spatialC1_of_spatialC3
      (
        momentumDiffusion0Component_spatialC3_of_H5
          h5 ht j
      )
      k

private theorem momentumDiffusion2Component_spatialC1_of_H5
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    (
      h5 :
        VelocitySpatialC5OnTail
          u a T
    )
    (
      ht :
        t ∈ Set.Ico a T
    )
    (k l j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        momentumDiffusion2Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t k l j
      ) := by

  unfold
    momentumDiffusion2Component
    momentumDiffusion1Component

  exact
    secondPartial_spatialC1_of_spatialC3
      (
        momentumDiffusion0Component_spatialC3_of_H5
          h5 ht j
      )
      k l

/-! ## Pressure -/

private theorem momentumPressure1Component_spatialC1_of_C4
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {a T t : ℝ}
    (
      h4 :
        PressureSpatialC4OnTail
          p a T
    )
    (
      ht :
        t ∈ Set.Ico a T
    )
    (k j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        momentumPressure1Component
          p t k j
      ) := by

  unfold
    momentumPressure1Component
    momentumPressure0Component

  exact
    firstPartial_spatialC1_of_spatialC3
      (h4 t ht j)
      k

private theorem momentumPressure2Component_spatialC1_of_C4
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {a T t : ℝ}
    (
      h4 :
        PressureSpatialC4OnTail
          p a T
    )
    (
      ht :
        t ∈ Set.Ico a T
    )
    (k l j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        momentumPressure2Component
          p t k l j
      ) := by

  unfold
    momentumPressure2Component
    momentumPressure1Component
    momentumPressure0Component

  exact
    secondPartial_spatialC1_of_spatialC3
      (h4 t ht j)
      k l

/-! ## Transport -/

/--
The first differentiated advection field is actually `SpatialC2` in the H3
energy class.  This is the useful nonlinear regularity statement: one more
spatial derivative therefore remains `SpatialC1`.
-/
private theorem momentumTransport1Component_spatialC2_of_energyClass
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
    {a T t : ℝ}
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
      h5 :
        VelocitySpatialC5OnTail
          u a T
    )
    (
      htNS :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      htTail :
        t ∈ Set.Ico a T
    )
    (k j : PrimeTensor.Axis Depth.three) :
    SpatialC2
      (
        momentumTransport1Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t k j
      ) := by

  let v :=
    PrimeTensor.Bridge.logSpaceTimeVectorField u

  let uj : ScalarField3 :=
    fun x =>
      (v t x).component j

  have hBase3
      (m : PrimeTensor.Axis Depth.three) :
      SpatialC3
        (
          fun x =>
            (v t x).component m
        ) := by

    simpa [v] using
      s.regularity.velocity_spatial_three
        t htNS m

  have hBase2
      (m : PrimeTensor.Axis Depth.three) :
      SpatialC2
        (
          fun x =>
            (v t x).component m
        ) :=
    spatialC2_of_spatialC3
      (hBase3 m)

  have hFirst2
      (m r : PrimeTensor.Axis Depth.three) :
      SpatialC2
        (
          spatial3.d r
            (
              fun x =>
                (v t x).component m
            )
        ) :=
    firstPartial_spatialC2_of_spatialC3
      (hBase3 m)
      r

  have hSecond2
      (r q : PrimeTensor.Axis Depth.three) :
      SpatialC2
        (
          spatial3.d r
            (
              spatial3.d q uj
            )
        ) := by

    have h3 :
        SpatialC3
          (
            spatial3.d r
              (
                spatial3.d q uj
              )
          ) := by

      simpa [uj, v, loggedVelocityComponent] using
        h5 t htTail j r q

    exact
      spatialC2_of_spatialC3
        h3

  have hExpanded :
      momentumTransport1Component
          v t k j
        =
      fun x =>
        (
          spatial3.d k
              (fun q => (v t q).component xAxis)
              x
            *
          spatial3.d xAxis uj x
          +
          (v t x).component xAxis
            *
          spatial3.d k
              (spatial3.d xAxis uj)
              x
        )
          +
        (
          (
            spatial3.d k
                (fun q => (v t q).component yAxis)
                x
              *
            spatial3.d yAxis uj x
            +
            (v t x).component yAxis
              *
            spatial3.d k
                (spatial3.d yAxis uj)
                x
          )
            +
          (
            spatial3.d k
                (fun q => (v t q).component zAxis)
                x
              *
            spatial3.d zAxis uj x
            +
            (v t x).component zAxis
              *
            spatial3.d k
                (spatial3.d zAxis uj)
                x
          )
        ) := by

    funext x

    unfold
      momentumTransport1Component
      momentumTransport0Component

    simpa [uj, v] using
      s.spatial_d_realAdvectionComponent
        htNS x k j

  rw [hExpanded]

  exact
    (
      (
        (hFirst2 xAxis k).mul
          (hFirst2 j xAxis)
      ).add
        (
          (hBase2 xAxis).mul
            (hSecond2 k xAxis)
        )
    ).add
      (
        (
          (
            (hFirst2 yAxis k).mul
              (hFirst2 j yAxis)
          ).add
            (
              (hBase2 yAxis).mul
                (hSecond2 k yAxis)
            )
        ).add
          (
            (
              (hFirst2 zAxis k).mul
                (hFirst2 j zAxis)
            ).add
              (
                (hBase2 zAxis).mul
                  (hSecond2 k zAxis)
              )
          )
      )

private theorem momentumTransport1Component_spatialC1_of_energyClass
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
    {a T t : ℝ}
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
      h5 :
        VelocitySpatialC5OnTail
          u a T
    )
    (
      htNS :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      htTail :
        t ∈ Set.Ico a T
    )
    (k j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        momentumTransport1Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t k j
      ) := by

  have h2 :=
    momentumTransport1Component_spatialC2_of_energyClass
      s h5 htNS htTail k j

  unfold SpatialC2 at h2
  unfold SpatialC1

  exact
    h2.of_le
      (by norm_num)

private theorem momentumTransport2Component_spatialC1_of_energyClass
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
    {a T t : ℝ}
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
      h5 :
        VelocitySpatialC5OnTail
          u a T
    )
    (
      htNS :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      htTail :
        t ∈ Set.Ico a T
    )
    (k l j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        momentumTransport2Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t k l j
      ) := by

  unfold momentumTransport2Component

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      (
        momentumTransport1Component_spatialC2_of_energyClass
          s h5 htNS htTail l j
      )
      k

/-! ## The class closes the full spatial-linearity package -/

/--
Every preterminal H3 energy class supplies a pressure witness for which the
complete higher-order momentum-split regularity holds at every interior tail
time.
-/
theorem preterminalH3EnergyClass_produces_splitRegularity
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
    ∃
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three,
        PreterminalNavierStokes3
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            p T
          ∧
        HigherOrderMomentumSplitRegularityAt
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            p t := by

  rcases hClass.pressure_witness with
    ⟨
      p,
      s,
      hp4
    ⟩

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨
      le_of_lt ht.1,
      ht.2
    ⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  refine
    ⟨
      p,
      s,
      ?_
    ⟩

  constructor

  · intro k j

    have hDiffusion :
        SpatialC1
          (
            momentumDiffusion1Component
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t k j
          ) :=
      momentumDiffusion1Component_spatialC1_of_H5
        hClass.velocity_spatial_five
        htTail
        k j

    have hTransport :
        SpatialC1
          (
            momentumTransport1Component
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t k j
          ) :=
      momentumTransport1Component_spatialC1_of_energyClass
        s
        hClass.velocity_spatial_five
        htNS
        htTail
        k j

    have hDiffusionTransport :
        SpatialC1
          (
            fun x =>
              momentumDiffusion1Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t k j x
                -
              momentumTransport1Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t k j x
          ) :=
      hDiffusion.sub hTransport

    have hPressure :
        SpatialC1
          (
            momentumPressure1Component
              p t k j
          ) :=
      momentumPressure1Component_spatialC1_of_C4
        hp4
        htTail
        k j

    exact
      ⟨
        hDiffusion,
        hTransport,
        hDiffusionTransport,
        hPressure
      ⟩

  · intro k l j

    have hDiffusion :
        SpatialC1
          (
            momentumDiffusion2Component
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t k l j
          ) :=
      momentumDiffusion2Component_spatialC1_of_H5
        hClass.velocity_spatial_five
        htTail
        k l j

    have hTransport :
        SpatialC1
          (
            momentumTransport2Component
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t k l j
          ) :=
      momentumTransport2Component_spatialC1_of_energyClass
        s
        hClass.velocity_spatial_five
        htNS
        htTail
        k l j

    have hDiffusionTransport :
        SpatialC1
          (
            fun x =>
              momentumDiffusion2Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t k l j x
                -
              momentumTransport2Component
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t k l j x
          ) :=
      hDiffusion.sub hTransport

    have hPressure :
        SpatialC1
          (
            momentumPressure2Component
              p t k l j
          ) :=
      momentumPressure2Component_spatialC1_of_C4
        hp4
        htTail
        k l j

    exact
      ⟨
        hDiffusion,
        hTransport,
        hDiffusionTransport,
        hPressure
      ⟩

/--
Consequently the actual higher-order momentum RHS split is automatic inside
the H3 energy class.
-/
theorem preterminalH3EnergyClass_produces_momentumRHSSplits
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
    ∃
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three,
        PreterminalNavierStokes3
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            p T
          ∧
        HigherOrderMomentumRHSSplitsAt
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            p t := by

  rcases
    preterminalH3EnergyClass_produces_splitRegularity
      hClass ht
  with
    ⟨
      p,
      s,
      hRegular
    ⟩

  exact
    ⟨
      p,
      s,
      higherOrderMomentumRHSSplitsAt_of_spatialC1
        hRegular
    ⟩

end Euclidean
end Bridge
end PrimeTensor
