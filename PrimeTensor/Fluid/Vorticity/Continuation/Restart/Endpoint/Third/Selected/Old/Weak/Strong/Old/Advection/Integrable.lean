import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Advection.Mass

/-!
# Endpoint-independent integrability of differentiated old advection

The previous increment closed the quantitative compact-test mass estimate for

    ∂ₐ ((u · ∇)uⱼ)

directly from `CanonicalH3TailDataFrom`.

The downstream pressure-free vorticity RHS assembly also needs the corresponding
`Integrable` statement as a reusable theorem.  The old `CurlTermIntegrable`
version carried endpoint continuity only through its six differentiated-product
integrability inputs.

Those six inputs are now endpoint-independent, so this file exports the same
six-product domination argument with no
`H3PreterminalCanonicalL2EndpointContinuousOnElapsed` hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldAdvectionIntegrable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongOldAdvectionIntegrable :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The compact-test-weighted differentiated old advection component is
integrable at every closed elapsed slice directly from the canonical H³ tail. -/
theorem integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_tailH3_weakStrong
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
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionFirstProduct_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a xAxis j

  have hfx2 : Integrable fx2 (volume : Measure Point3) := by
    dsimp only [fx2]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionSecondProduct_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a xAxis j

  have hfy1 : Integrable fy1 (volume : Measure Point3) := by
    dsimp only [fy1]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionFirstProduct_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a yAxis j

  have hfy2 : Integrable fy2 (volume : Measure Point3) := by
    dsimp only [fy2]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionSecondProduct_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a yAxis j

  have hfz1 : Integrable fz1 (volume : Measure Point3) := by
    dsimp only [fz1]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionFirstProduct_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a zAxis j

  have hfz2 : Integrable fz2 (volume : Measure Point3) := by
    dsimp only [fz2]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionSecondProduct_tailH3_weakStrong
        hNS ht hEnd hE hTail
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
