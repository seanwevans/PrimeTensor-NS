import PrimeTensor.Fluid.VorticitySecondJetContinuity
import PrimeTensor.Bridge.EuclideanThirdPartials
import PrimeTensor.Bridge.EuclideanCurlLaplacianX

/-!
# Third-velocity-jet continuity for the moving-time vorticity cascade

The preceding continuation layer assumes time continuity of the same-axis second
derivatives of classical vorticity.  Since vorticity is the curl of the logged
velocity, these are third spatial derivatives of the logged velocity.

This file makes that expansion explicit without commuting third partials.
For example,

    ∂ᵢ² ωₓ
      = ∂ᵢ² (∂y u_z - ∂z u_y)
      = ∂ᵢ² ∂y u_z - ∂ᵢ² ∂z u_y.

The second equality only needs:

* each logged velocity component to be spatially `C³` on every time slice;
* the already-proved fact that a first partial of a `C³` field is `C²`;
* linearity of a pure second partial across subtraction.

No third-order Schwarz permutation is needed for this layer.

We package ordinary time continuity of the complete third spatial jet

    t ↦ ∂a ∂b ∂c (log u_j)(t,x)

and show that it implies all three vorticity-second-jet continuity predicates.
The final continuation criteria are therefore stated entirely in velocity-jet
language: first-jet time continuity, third-jet time continuity, and spatial
`C³` regularity of the logged velocity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
Every logged velocity component is spatially `C³` on every fixed time slice.
-/
def VelocityLogSpatialC3
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    ) : Prop :=
  ∀ (t : ℝ)
    (j : PrimeTensor.Axis Depth.three),
      SpatialC3
        (
          fun y =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y
            ).component j
        )

/--
Time continuity at `(T,x)` of the complete third spatial jet of the logged
velocity.

The derivative ordering is left explicit.  No mixed-partial commutation is
built into this definition.
-/
def VelocityThirdJetLogContinuousAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (x : Point3) : Prop :=
  ∀
    (a b c j :
      PrimeTensor.Axis Depth.three),
    ContinuousAt
      (
        fun t =>
          spatial3.d
            a
            (
              spatial3.d
                b
                (
                  spatial3.d
                    c
                    (
                      fun y =>
                        (
                          PrimeTensor.Bridge.logSpaceTimeVectorField
                            u t y
                        ).component j
                    )
                )
            )
            x
      )
      T

/--
The first and third logged velocity jets are both time-continuous at `(T,x)`.
-/
def VelocityContinuationJetLogContinuousAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (x : Point3) : Prop :=
  VelocityFirstJetLogContinuousAt u T x ∧
  VelocityThirdJetLogContinuousAt u T x

/--
A first partial of one logged velocity component is spatially `C²`.
-/
theorem loggedVelocity_firstPartial_spatialC2
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (t : ℝ)
    (
      c j :
        PrimeTensor.Axis Depth.three
    ) :
    SpatialC2
      (
        spatial3.d
          c
          (
            fun y =>
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u t y
              ).component j
          )
      ) := by

  have hC3 :=
    hSpatial t j

  change
    SpatialC2
      (
        fun y =>
          partialDeriv
            c
            (
              fun q =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t q
                ).component j
            )
            y
      )

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hC3 c

/--
Pure second differentiation of x-vorticity expands into the corresponding
difference of third logged-velocity derivatives.
-/
theorem secondPartial_realVorticityX_eq_thirdVelocity
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (t : ℝ)
    (x : Point3)
    (
      i :
        PrimeTensor.Axis Depth.three
    ) :
    spatial3.d
        i
        (
          spatial3.d
            i
            (
              fun y =>
                realVorticityX
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t y
            )
        )
        x
      =
    spatial3.d
        i
        (
          spatial3.d
            i
            (
              spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component zAxis
                )
            )
        )
        x
      -
    spatial3.d
        i
        (
          spatial3.d
            i
            (
              spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component yAxis
                )
            )
        )
        x := by

  have hy :
      SpatialC2
        (
          spatial3.d
            yAxis
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component zAxis
            )
        ) :=
    loggedVelocity_firstPartial_spatialC2
      hSpatial t yAxis zAxis

  have hz :
      SpatialC2
        (
          spatial3.d
            zAxis
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component yAxis
            )
        ) :=
    loggedVelocity_firstPartial_spatialC2
      hSpatial t zAxis yAxis

  unfold realVorticityX

  simpa only [spatial3] using
    (
      PrimeTensor.Bridge.Euclidean.SpatialC2.secondPartial_sub
        hy hz x i
    )

/-- Y-vorticity analogue of the third-velocity-derivative expansion. -/
theorem secondPartial_realVorticityY_eq_thirdVelocity
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (t : ℝ)
    (x : Point3)
    (
      i :
        PrimeTensor.Axis Depth.three
    ) :
    spatial3.d
        i
        (
          spatial3.d
            i
            (
              fun y =>
                realVorticityY
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t y
            )
        )
        x
      =
    spatial3.d
        i
        (
          spatial3.d
            i
            (
              spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
            )
        )
        x
      -
    spatial3.d
        i
        (
          spatial3.d
            i
            (
              spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component zAxis
                )
            )
        )
        x := by

  have hz :
      SpatialC2
        (
          spatial3.d
            zAxis
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component xAxis
            )
        ) :=
    loggedVelocity_firstPartial_spatialC2
      hSpatial t zAxis xAxis

  have hx :
      SpatialC2
        (
          spatial3.d
            xAxis
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component zAxis
            )
        ) :=
    loggedVelocity_firstPartial_spatialC2
      hSpatial t xAxis zAxis

  unfold realVorticityY

  simpa only [spatial3] using
    (
      PrimeTensor.Bridge.Euclidean.SpatialC2.secondPartial_sub
        hz hx x i
    )

/-- Z-vorticity analogue of the third-velocity-derivative expansion. -/
theorem secondPartial_realVorticityZ_eq_thirdVelocity
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (t : ℝ)
    (x : Point3)
    (
      i :
        PrimeTensor.Axis Depth.three
    ) :
    spatial3.d
        i
        (
          spatial3.d
            i
            (
              fun y =>
                realVorticityZ
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t y
            )
        )
        x
      =
    spatial3.d
        i
        (
          spatial3.d
            i
            (
              spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component yAxis
                )
            )
        )
        x
      -
    spatial3.d
        i
        (
          spatial3.d
            i
            (
              spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
            )
        )
        x := by

  have hx :
      SpatialC2
        (
          spatial3.d
            xAxis
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component yAxis
            )
        ) :=
    loggedVelocity_firstPartial_spatialC2
      hSpatial t xAxis yAxis

  have hy :
      SpatialC2
        (
          spatial3.d
            yAxis
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component xAxis
            )
        ) :=
    loggedVelocity_firstPartial_spatialC2
      hSpatial t yAxis xAxis

  unfold realVorticityZ

  simpa only [spatial3] using
    (
      PrimeTensor.Bridge.Euclidean.SpatialC2.secondPartial_sub
        hx hy x i
    )

/--
Complete third-jet time continuity implies x-vorticity second-jet continuity.
-/
theorem vorticitySecondJetXContinuousAt_of_thirdJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    {x : Point3}
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hThird :
        VelocityThirdJetLogContinuousAt
          u T x
    ) :
    VorticitySecondJetXContinuousAt
      u T x := by

  intro i

  have hSub :=
    (
      hThird i i yAxis zAxis
    ).sub
      (
        hThird i i zAxis yAxis
      )

  have hPointwise :
      (
        (
          fun t =>
            spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component zAxis
                      )
                  )
              )
              x
        )
          -
        (
          fun t =>
            spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component yAxis
                      )
                  )
              )
              x
        )
      )
        =
      (
        fun t =>
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component zAxis
                      )
                  )
              )
              x
            -
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component yAxis
                      )
                  )
              )
              x
      ) := by

    funext t
    rfl

  rw [hPointwise] at hSub

  have hFunctions :
      (
        fun t =>
          spatial3.d
            i
            (
              spatial3.d
                i
                (
                  fun y =>
                    realVorticityX
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      t y
                )
            )
            x
      )
        =
      (
        fun t =>
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component zAxis
                      )
                  )
              )
              x
            -
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component yAxis
                      )
                  )
              )
              x
      ) := by

    funext t

    exact
      secondPartial_realVorticityX_eq_thirdVelocity
        hSpatial t x i

  rw [hFunctions]

  exact hSub

/-- Complete third-jet time continuity implies y-vorticity second-jet continuity. -/
theorem vorticitySecondJetYContinuousAt_of_thirdJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    {x : Point3}
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hThird :
        VelocityThirdJetLogContinuousAt
          u T x
    ) :
    VorticitySecondJetYContinuousAt
      u T x := by

  intro i

  have hSub :=
    (
      hThird i i zAxis xAxis
    ).sub
      (
        hThird i i xAxis zAxis
      )

  have hPointwise :
      (
        (
          fun t =>
            spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component xAxis
                      )
                  )
              )
              x
        )
          -
        (
          fun t =>
            spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component zAxis
                      )
                  )
              )
              x
        )
      )
        =
      (
        fun t =>
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component xAxis
                      )
                  )
              )
              x
            -
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component zAxis
                      )
                  )
              )
              x
      ) := by

    funext t
    rfl

  rw [hPointwise] at hSub

  have hFunctions :
      (
        fun t =>
          spatial3.d
            i
            (
              spatial3.d
                i
                (
                  fun y =>
                    realVorticityY
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      t y
                )
            )
            x
      )
        =
      (
        fun t =>
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component xAxis
                      )
                  )
              )
              x
            -
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component zAxis
                      )
                  )
              )
              x
      ) := by

    funext t

    exact
      secondPartial_realVorticityY_eq_thirdVelocity
        hSpatial t x i

  rw [hFunctions]

  exact hSub

/-- Complete third-jet time continuity implies z-vorticity second-jet continuity. -/
theorem vorticitySecondJetZContinuousAt_of_thirdJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    {x : Point3}
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hThird :
        VelocityThirdJetLogContinuousAt
          u T x
    ) :
    VorticitySecondJetZContinuousAt
      u T x := by

  intro i

  have hSub :=
    (
      hThird i i xAxis yAxis
    ).sub
      (
        hThird i i yAxis xAxis
      )

  have hPointwise :
      (
        (
          fun t =>
            spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component yAxis
                      )
                  )
              )
              x
        )
          -
        (
          fun t =>
            spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component xAxis
                      )
                  )
              )
              x
        )
      )
        =
      (
        fun t =>
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component yAxis
                      )
                  )
              )
              x
            -
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component xAxis
                      )
                  )
              )
              x
      ) := by

    funext t
    rfl

  rw [hPointwise] at hSub

  have hFunctions :
      (
        fun t =>
          spatial3.d
            i
            (
              spatial3.d
                i
                (
                  fun y =>
                    realVorticityZ
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      t y
                )
            )
            x
      )
        =
      (
        fun t =>
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component yAxis
                      )
                  )
              )
              x
            -
          spatial3.d
              i
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component xAxis
                      )
                  )
              )
              x
      ) := by

    funext t

    exact
      secondPartial_realVorticityZ_eq_thirdVelocity
        hSpatial t x i

  rw [hFunctions]

  exact hSub

/--
Complete third-jet time continuity supplies all three vorticity second-jet
continuity predicates.
-/
theorem vorticitySecondJetContinuousAt_of_thirdJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    {x : Point3}
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hThird :
        VelocityThirdJetLogContinuousAt
          u T x
    ) :
    VorticitySecondJetContinuousAt
      u T x := by

  exact
    ⟨
      vorticitySecondJetXContinuousAt_of_thirdJet
        hSpatial hThird,
      vorticitySecondJetYContinuousAt_of_thirdJet
        hSpatial hThird,
      vorticitySecondJetZContinuousAt_of_thirdJet
        hSpatial hThird
    ⟩

/--
X-component continuation criterion stated entirely with logged velocity jets.
-/
theorem noCofinalVorticityBalancePathX_of_velocityJets
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
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceX
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceX
          u T x
    )
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hJets :
        VelocityContinuationJetLogContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathX
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  exact
    noCofinalVorticityBalancePathX_of_continuousJets
      hτ
      hStages
      hLimit
      hJets.1
      (
        vorticitySecondJetXContinuousAt_of_thirdJet
          hSpatial hJets.2
      )

/-- Y-component continuation criterion stated entirely with logged velocity jets. -/
theorem noCofinalVorticityBalancePathY_of_velocityJets
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
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceY
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceY
          u T x
    )
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hJets :
        VelocityContinuationJetLogContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathY
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  exact
    noCofinalVorticityBalancePathY_of_continuousJets
      hτ
      hStages
      hLimit
      hJets.1
      (
        vorticitySecondJetYContinuousAt_of_thirdJet
          hSpatial hJets.2
      )

/-- Z-component continuation criterion stated entirely with logged velocity jets. -/
theorem noCofinalVorticityBalancePathZ_of_velocityJets
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
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceZ
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceZ
          u T x
    )
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hJets :
        VelocityContinuationJetLogContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathZ
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  exact
    noCofinalVorticityBalancePathZ_of_continuousJets
      hτ
      hStages
      hLimit
      hJets.1
      (
        vorticitySecondJetZContinuousAt_of_thirdJet
          hSpatial hJets.2
      )

end Euclidean
end Bridge
end PrimeTensor
