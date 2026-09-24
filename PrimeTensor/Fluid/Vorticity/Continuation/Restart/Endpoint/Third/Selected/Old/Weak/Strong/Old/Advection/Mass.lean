import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Advection.Product.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.AdvectionTriangle

/-!
# Endpoint-independent differentiated-advection mass

The old endpoint `AdvectionMass` theorem is algebraically pressure-free.  Its
only dependence on endpoint continuity came through the six product
integrability and product-mass inputs.

Those inputs have now been rebuilt directly from `CanonicalH3TailDataFrom`.
This file ports the full six-term differentiated-advection mass estimate
without `H3PreterminalCanonicalL2EndpointContinuousOnElapsed`.

The numerical envelope and its syntactic shape are intentionally preserved so
the downstream vorticity RHS mass files can be ported with minimal changes.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldAdvectionMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongOldAdvectionMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Uniform compact-test spatial mass bound for one spatial derivative of one
old logged advection component, directly from the canonical H³ tail. -/
theorem integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_le_tailH3_weakStrong
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
    (∫ x : Point3,
        ‖ψ x‖ *
          ‖spatial3.d
              a
              (fun y =>
                realAdvectionComponent
                  (logSpaceTimeVectorField u)
                  (t + (q : ℝ))
                  y
                  j)
              x‖
      ∂volume)
      ≤
    (
      (
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      )
      +
      (
        h3RawFourierL1DeweightingCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      )
    )
      +
    (
      (
        (
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            (2 * E)
        )
          *
        (
          h3WeakTestFunctionL2Mass ψ *
            (2 * E) ^ (1 / (2 : ℝ))
        )
        +
        (
          h3RawFourierL1DeweightingCoefficient *
            (2 * E)
        )
          *
        (
          h3WeakTestFunctionL2Mass ψ *
            (2 * E) ^ (1 / (2 : ℝ))
        )
      )
        +
      (
        (
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            (2 * E)
        )
          *
        (
          h3WeakTestFunctionL2Mass ψ *
            (2 * E) ^ (1 / (2 : ℝ))
        )
        +
        (
          h3RawFourierL1DeweightingCoefficient *
            (2 * E)
        )
          *
        (
          h3WeakTestFunctionL2Mass ψ *
            (2 * E) ^ (1 / (2 : ℝ))
        )
      )
    ) := by
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

  have hIntegralLe :
      (∫ x : Point3,
          ‖ψ x‖ * ‖adv x‖
        ∂volume)
        ≤
      ∫ x : Point3, major x ∂volume :=
    integral_mono_ae
      hTargetInt
      hMajorInt
      (Filter.Eventually.of_forall hPoint)

  have hMajorIntegral :
      (∫ x : Point3, major x ∂volume)
        =
      ((∫ x : Point3, fx1 x ∂volume) +
        (∫ x : Point3, fx2 x ∂volume))
        +
      (
        ((∫ x : Point3, fy1 x ∂volume) +
          (∫ x : Point3, fy2 x ∂volume))
        +
        ((∫ x : Point3, fz1 x ∂volume) +
          (∫ x : Point3, fz2 x ∂volume))
      ) := by
    have hOuter :
        (∫ x : Point3,
            (fx1 x + fx2 x) +
              ((fy1 x + fy2 x) + (fz1 x + fz2 x))
          ∂volume)
          =
        (∫ x : Point3, fx1 x + fx2 x ∂volume)
          +
        (∫ x : Point3,
            (fy1 x + fy2 x) + (fz1 x + fz2 x)
          ∂volume) := by
      exact
        integral_add
          (hfx1.add hfx2)
          ((hfy1.add hfy2).add (hfz1.add hfz2))

    have hX :
        (∫ x : Point3, fx1 x + fx2 x ∂volume)
          =
        (∫ x : Point3, fx1 x ∂volume)
          +
        (∫ x : Point3, fx2 x ∂volume) := by
      exact integral_add hfx1 hfx2

    have hYZ :
        (∫ x : Point3,
            (fy1 x + fy2 x) + (fz1 x + fz2 x)
          ∂volume)
          =
        (∫ x : Point3, fy1 x + fy2 x ∂volume)
          +
        (∫ x : Point3, fz1 x + fz2 x ∂volume) := by
      exact
        integral_add
          (hfy1.add hfy2)
          (hfz1.add hfz2)

    have hY :
        (∫ x : Point3, fy1 x + fy2 x ∂volume)
          =
        (∫ x : Point3, fy1 x ∂volume)
          +
        (∫ x : Point3, fy2 x ∂volume) := by
      exact integral_add hfy1 hfy2

    have hZ :
        (∫ x : Point3, fz1 x + fz2 x ∂volume)
          =
        (∫ x : Point3, fz1 x ∂volume)
          +
        (∫ x : Point3, fz2 x ∂volume) := by
      exact integral_add hfz1 hfz2

    dsimp only [major]
    calc
      (∫ x : Point3,
          fx1 x + fx2 x +
            (fy1 x + fy2 x + (fz1 x + fz2 x))
        ∂volume)
          =
        (∫ x : Point3, fx1 x + fx2 x ∂volume)
          +
        (∫ x : Point3,
            (fy1 x + fy2 x) + (fz1 x + fz2 x)
          ∂volume) := hOuter
      _ =
        ((∫ x : Point3, fx1 x ∂volume) +
          (∫ x : Point3, fx2 x ∂volume))
          +
        (∫ x : Point3,
            (fy1 x + fy2 x) + (fz1 x + fz2 x)
          ∂volume) := by rw [hX]
      _ =
        ((∫ x : Point3, fx1 x ∂volume) +
          (∫ x : Point3, fx2 x ∂volume))
          +
        (
          (∫ x : Point3, fy1 x + fy2 x ∂volume)
            +
          (∫ x : Point3, fz1 x + fz2 x ∂volume)
        ) := by rw [hYZ]
      _ =
        ((∫ x : Point3, fx1 x ∂volume) +
          (∫ x : Point3, fx2 x ∂volume))
          +
        (
          ((∫ x : Point3, fy1 x ∂volume) +
            (∫ x : Point3, fy2 x ∂volume))
            +
          (∫ x : Point3, fz1 x + fz2 x ∂volume)
        ) := by rw [hY]
      _ =
        ((∫ x : Point3, fx1 x ∂volume) +
          (∫ x : Point3, fx2 x ∂volume))
          +
        (
          ((∫ x : Point3, fy1 x ∂volume) +
            (∫ x : Point3, fy2 x ∂volume))
            +
          ((∫ x : Point3, fz1 x ∂volume) +
            (∫ x : Point3, fz2 x ∂volume))
        ) := by rw [hZ]

  have hBx1 :
      (∫ x : Point3, fx1 x ∂volume)
        ≤
      (
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      ) := by
    dsimp only [fx1]
    simpa only [
      h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
    ] using
      integral_weakTest_norm_mul_norm_loggedVelocityComponent_spatial_d_mul_spatial_d_le_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a xAxis j

  have hBx2 :
      (∫ x : Point3, fx2 x ∂volume)
        ≤
      (
        h3RawFourierL1DeweightingCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      ) := by
    dsimp only [fx2]
    simpa only [
      h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
    ] using
      integral_weakTest_norm_mul_norm_loggedVelocityComponent_mul_spatial_d2_le_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a xAxis j

  have hBy1 :
      (∫ x : Point3, fy1 x ∂volume)
        ≤
      (
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      ) := by
    dsimp only [fy1]
    simpa only [
      h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
    ] using
      integral_weakTest_norm_mul_norm_loggedVelocityComponent_spatial_d_mul_spatial_d_le_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a yAxis j

  have hBy2 :
      (∫ x : Point3, fy2 x ∂volume)
        ≤
      (
        h3RawFourierL1DeweightingCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      ) := by
    dsimp only [fy2]
    simpa only [
      h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
    ] using
      integral_weakTest_norm_mul_norm_loggedVelocityComponent_mul_spatial_d2_le_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a yAxis j

  have hBz1 :
      (∫ x : Point3, fz1 x ∂volume)
        ≤
      (
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      ) := by
    dsimp only [fz1]
    simpa only [
      h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
    ] using
      integral_weakTest_norm_mul_norm_loggedVelocityComponent_spatial_d_mul_spatial_d_le_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a zAxis j

  have hBz2 :
      (∫ x : Point3, fz2 x ∂volume)
        ≤
      (
        h3RawFourierL1DeweightingCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      ) := by
    dsimp only [fz2]
    simpa only [
      h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
    ] using
      integral_weakTest_norm_mul_norm_loggedVelocityComponent_mul_spatial_d2_le_tailH3_weakStrong
        hNS ht hEnd hE hTail
        ψ q a zAxis j

  rw [hMajorIntegral] at hIntegralLe

  dsimp only [adv] at hIntegralLe
  exact
    hIntegralLe.trans
      (by
        gcongr)

end

end Euclidean
end Bridge
end PrimeTensor
