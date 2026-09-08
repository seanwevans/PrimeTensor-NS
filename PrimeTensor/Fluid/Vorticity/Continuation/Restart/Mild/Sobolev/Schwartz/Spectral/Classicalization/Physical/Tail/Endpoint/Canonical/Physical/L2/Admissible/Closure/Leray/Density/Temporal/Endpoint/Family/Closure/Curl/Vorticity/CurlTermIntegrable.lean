import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.RHSTriangle

/-!
# Integrability of the endpoint curl building blocks

`AdvectionMass` and `DiffusionMass` each prove the integrability needed for
their final integral comparison internally.  The final x/y/z vorticity RHS
assembly needs those same facts repeatedly, so this file exports them in
reusable form.

The two statements are:

* compact-test-weighted `∂ₐ Δuⱼ` is integrable;
* compact-test-weighted `∂ₐ ((u · ∇)uⱼ)` is integrable.

No new estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlTermIntegrable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlTermIntegrable :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The compact-test-weighted differentiated componentwise Laplacian is
integrable at every closed endpoint slice. -/
theorem integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (a j : PrimeTensor.Axis Depth.three) :
    Integrable
      (fun x : Point3 =>
        ‖ψ x‖ *
          ‖spatial3.d
              a
              (PrimeTensor.Bridge.RealFluid.laplacian
                spatial3
                (loggedVelocityComponent
                  u (t + (q : ℝ)) j))
              x‖)
      (volume : Measure Point3) := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  let pOld : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  let f : ScalarField3 :=
    loggedVelocityComponent
      u (t + (q : ℝ)) j

  have hf3 : SpatialC3 f := by
    dsimp only [f]
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) x).component j)
    exact
      hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ)) hs j

  let tx : ScalarField3 :=
    spatial3.d
      a
      (spatial3.d
        xAxis
        (spatial3.d xAxis f))

  let ty : ScalarField3 :=
    spatial3.d
      a
      (spatial3.d
        yAxis
        (spatial3.d yAxis f))

  let tz : ScalarField3 :=
    spatial3.d
      a
      (spatial3.d
        zAxis
        (spatial3.d zAxis f))

  let diff : ScalarField3 :=
    spatial3.d
      a
      (PrimeTensor.Bridge.RealFluid.laplacian
        spatial3 f)

  have hDiffEq :
      diff =
        fun x =>
          tx x + (ty x + tz x) := by
    funext x
    dsimp only [diff, tx, ty, tz]
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_laplacian3
        hf3 x a

  have hMeas :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  have hj := hMeas j
  dsimp only at hj

  have htxMeas :
      AEStronglyMeasurable
        tx
        (volume : Measure Point3) := by
    dsimp only [tx, f]
    exact hj.2.2.2 a xAxis xAxis

  have htyMeas :
      AEStronglyMeasurable
        ty
        (volume : Measure Point3) := by
    dsimp only [ty, f]
    exact hj.2.2.2 a yAxis yAxis

  have htzMeas :
      AEStronglyMeasurable
        tz
        (volume : Measure Point3) := by
    dsimp only [tz, f]
    exact hj.2.2.2 a zAxis zAxis

  have hDiffMeas :
      AEStronglyMeasurable
        diff
        (volume : Measure Point3) := by
    rw [hDiffEq]
    exact htxMeas.add (htyMeas.add htzMeas)

  let gx : Point3 → ℝ :=
    fun x => ‖ψ x‖ * ‖tx x‖

  let gy : Point3 → ℝ :=
    fun x => ‖ψ x‖ * ‖ty x‖

  let gz : Point3 → ℝ :=
    fun x => ‖ψ x‖ * ‖tz x‖

  have hgxInt :
      Integrable gx (volume : Measure Point3) := by
    dsimp only [gx, tx, f]
    exact
      integrable_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_endpoint
        hNS ht hEnd hE hTail
        ψ q a xAxis xAxis j

  have hgyInt :
      Integrable gy (volume : Measure Point3) := by
    dsimp only [gy, ty, f]
    exact
      integrable_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_endpoint
        hNS ht hEnd hE hTail
        ψ q a yAxis yAxis j

  have hgzInt :
      Integrable gz (volume : Measure Point3) := by
    dsimp only [gz, tz, f]
    exact
      integrable_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_endpoint
        hNS ht hEnd hE hTail
        ψ q a zAxis zAxis j

  let major : Point3 → ℝ :=
    fun x =>
      gx x + (gy x + gz x)

  have hMajorInt :
      Integrable major (volume : Measure Point3) := by
    dsimp only [major]
    exact hgxInt.add (hgyInt.add hgzInt)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          ‖ψ x‖ * ‖diff x‖)
        (volume : Measure Point3) :=
    ψ.continuous.aestronglyMeasurable.norm.mul
      hDiffMeas.norm

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ * ‖diff x‖
          ≤
        major x := by
    intro x
    have hNorm :
        ‖diff x‖
          ≤
        ‖tx x‖ + (‖ty x‖ + ‖tz x‖) := by
      rw [hDiffEq]
      exact
        (norm_add_le
          (tx x)
          (ty x + tz x)).trans
          (add_le_add
            (le_refl ‖tx x‖)
            (norm_add_le (ty x) (tz x)))

    have hWeighted :=
      mul_le_mul_of_nonneg_left
        hNorm
        (norm_nonneg (ψ x))

    dsimp only [major, gx, gy, gz]
    simpa only [mul_add] using hWeighted

  have hTargetInt :
      Integrable
        (fun x : Point3 =>
          ‖ψ x‖ * ‖diff x‖)
        (volume : Measure Point3) := by
    refine
      hMajorInt.mono'
        hTargetMeas
        (Filter.Eventually.of_forall ?_)
    intro x
    rw [
      Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg
          (norm_nonneg (ψ x))
          (norm_nonneg (diff x)))
    ]
    exact hPoint x

  simpa only [diff, f] using hTargetInt

/-- The compact-test-weighted differentiated advection component is integrable
at every closed endpoint slice. -/
theorem integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (a j : PrimeTensor.Axis Depth.three) :
    Integrable
      (fun x : Point3 =>
        ‖ψ x‖ *
          ‖spatial3.d
              a
              (fun y =>
                realAdvectionComponent
                  (logSpaceTimeVectorField u)
                  (t + (q : ℝ))
                  y
                  j)
              x‖)
      (volume : Measure Point3) := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  let fx1 : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
            u (t + (q : ℝ)) a xAxis j x‖

  let fx2 : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
            u (t + (q : ℝ)) a xAxis j x‖

  let fy1 : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
            u (t + (q : ℝ)) a yAxis j x‖

  let fy2 : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
            u (t + (q : ℝ)) a yAxis j x‖

  let fz1 : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
            u (t + (q : ℝ)) a zAxis j x‖

  let fz2 : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
            u (t + (q : ℝ)) a zAxis j x‖

  have hfx1 : Integrable fx1 (volume : Measure Point3) := by
    dsimp only [fx1]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
        hNS ht hEnd hE hTail hEndpoint
        ψ q a xAxis j

  have hfx2 : Integrable fx2 (volume : Measure Point3) := by
    dsimp only [fx2]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
        hNS ht hEnd hE hTail hEndpoint
        ψ q a xAxis j

  have hfy1 : Integrable fy1 (volume : Measure Point3) := by
    dsimp only [fy1]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
        hNS ht hEnd hE hTail hEndpoint
        ψ q a yAxis j

  have hfy2 : Integrable fy2 (volume : Measure Point3) := by
    dsimp only [fy2]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
        hNS ht hEnd hE hTail hEndpoint
        ψ q a yAxis j

  have hfz1 : Integrable fz1 (volume : Measure Point3) := by
    dsimp only [fz1]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
        hNS ht hEnd hE hTail hEndpoint
        ψ q a zAxis j

  have hfz2 : Integrable fz2 (volume : Measure Point3) := by
    dsimp only [fz2]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
        hNS ht hEnd hE hTail hEndpoint
        ψ q a zAxis j

  let major : Point3 → ℝ :=
    fun x =>
      (fx1 x + fx2 x) +
        ((fy1 x + fy2 x) + (fz1 x + fz2 x))

  have hMajorInt :
      Integrable major (volume : Measure Point3) := by
    dsimp only [major]
    exact
      (hfx1.add hfx2).add
        ((hfy1.add hfy2).add (hfz1.add hfz2))

  have hMeas :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  have hx := hMeas xAxis
  have hy := hMeas yAxis
  have hz := hMeas zAxis
  have hj := hMeas j
  dsimp only at hx hy hz hj

  let adv : ScalarField3 :=
    fun x =>
      spatial3.d
        a
        (fun y =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            y
            j)
        x

  let expanded : ScalarField3 :=
    fun x =>
      (
        spatial3.d
            a
            (fun y =>
              (logSpaceTimeVectorField
                u (t + (q : ℝ)) y).component xAxis)
            x
          *
        spatial3.d
            xAxis
            (fun y =>
              (logSpaceTimeVectorField
                u (t + (q : ℝ)) y).component j)
            x
        +
        (logSpaceTimeVectorField
            u (t + (q : ℝ)) x).component xAxis
          *
        spatial3.d
            a
            (spatial3.d
              xAxis
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component j))
            x
      )
        +
      (
        (
          spatial3.d
              a
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component yAxis)
              x
            *
          spatial3.d
              yAxis
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component j)
              x
          +
          (logSpaceTimeVectorField
              u (t + (q : ℝ)) x).component yAxis
            *
          spatial3.d
              a
              (spatial3.d
                yAxis
                (fun y =>
                  (logSpaceTimeVectorField
                    u (t + (q : ℝ)) y).component j))
              x
        )
          +
        (
          spatial3.d
              a
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component zAxis)
              x
            *
          spatial3.d
              zAxis
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component j)
              x
          +
          (logSpaceTimeVectorField
              u (t + (q : ℝ)) x).component zAxis
            *
          spatial3.d
              a
              (spatial3.d
                zAxis
                (fun y =>
                  (logSpaceTimeVectorField
                    u (t + (q : ℝ)) y).component j))
              x
        )
      )

  have hExpandedMeas :
      AEStronglyMeasurable
        expanded
        (volume : Measure Point3) := by
    have hRaw :
        AEStronglyMeasurable
          (fun x =>
            (
              spatial3.d
                  a
                  (loggedVelocityComponent
                    u (t + (q : ℝ)) xAxis)
                  x
                *
              spatial3.d
                  xAxis
                  (loggedVelocityComponent
                    u (t + (q : ℝ)) j)
                  x
              +
              loggedVelocityComponent
                  u (t + (q : ℝ)) xAxis x
                *
              spatial3.d
                  a
                  (spatial3.d
                    xAxis
                    (loggedVelocityComponent
                      u (t + (q : ℝ)) j))
                  x
            )
              +
            (
              (
                spatial3.d
                    a
                    (loggedVelocityComponent
                      u (t + (q : ℝ)) yAxis)
                    x
                  *
                spatial3.d
                    yAxis
                    (loggedVelocityComponent
                      u (t + (q : ℝ)) j)
                    x
                +
                loggedVelocityComponent
                    u (t + (q : ℝ)) yAxis x
                  *
                spatial3.d
                    a
                    (spatial3.d
                      yAxis
                      (loggedVelocityComponent
                        u (t + (q : ℝ)) j))
                    x
              )
                +
              (
                spatial3.d
                    a
                    (loggedVelocityComponent
                      u (t + (q : ℝ)) zAxis)
                    x
                  *
                spatial3.d
                    zAxis
                    (loggedVelocityComponent
                      u (t + (q : ℝ)) j)
                    x
                +
                loggedVelocityComponent
                    u (t + (q : ℝ)) zAxis x
                  *
                spatial3.d
                    a
                    (spatial3.d
                      zAxis
                      (loggedVelocityComponent
                        u (t + (q : ℝ)) j))
                    x
              )
            ))
          (volume : Measure Point3) :=
      ((hx.2.1 a).mul (hj.2.1 xAxis)).add
        (hx.1.mul (hj.2.2.1 a xAxis))
      |>.add
        (
          (((hy.2.1 a).mul (hj.2.1 yAxis)).add
            (hy.1.mul (hj.2.2.1 a yAxis)))
          |>.add
            (((hz.2.1 a).mul (hj.2.1 zAxis)).add
              (hz.1.mul (hj.2.2.1 a zAxis)))
        )

    have hxEq :
        loggedVelocityComponent
            u (t + (q : ℝ)) xAxis
          =
        fun y =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component xAxis := by
      rfl

    have hyEq :
        loggedVelocityComponent
            u (t + (q : ℝ)) yAxis
          =
        fun y =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component yAxis := by
      rfl

    have hzEq :
        loggedVelocityComponent
            u (t + (q : ℝ)) zAxis
          =
        fun y =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component zAxis := by
      rfl

    have hjEq :
        loggedVelocityComponent
            u (t + (q : ℝ)) j
          =
        fun y =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) y).component j := by
      rfl

    dsimp only [expanded]
    rw [← hxEq, ← hyEq, ← hzEq, ← hjEq]
    exact hRaw

  have hAdvEq :
      adv = expanded := by
    funext x
    dsimp only [adv, expanded]
    exact
      h3LoggedPreterminal_spatial_d_realAdvectionComponent
        hNS hs x a j

  have hAdvMeas :
      AEStronglyMeasurable
        adv
        (volume : Measure Point3) := by
    rw [hAdvEq]
    exact hExpandedMeas

  have hTargetMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          ‖ψ x‖ * ‖adv x‖)
        (volume : Measure Point3) :=
    ψ.continuous.aestronglyMeasurable.norm.mul
      hAdvMeas.norm

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ * ‖adv x‖ ≤ major x := by
    intro x
    dsimp only [adv, major, fx1, fx2, fy1, fy2, fz1, fz2]
    exact
      weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_le_sixProducts
        hNS hs ψ x a j

  have hTargetInt :
      Integrable
        (fun x : Point3 =>
          ‖ψ x‖ * ‖adv x‖)
        (volume : Measure Point3) := by
    refine
      hMajorInt.mono'
        hTargetMeas
        (Filter.Eventually.of_forall ?_)
    intro x
    rw [
      Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg
          (norm_nonneg (ψ x))
          (norm_nonneg (adv x)))
    ]
    exact hPoint x

  simpa only [adv] using hTargetInt

end

end Euclidean
end Bridge
end PrimeTensor
