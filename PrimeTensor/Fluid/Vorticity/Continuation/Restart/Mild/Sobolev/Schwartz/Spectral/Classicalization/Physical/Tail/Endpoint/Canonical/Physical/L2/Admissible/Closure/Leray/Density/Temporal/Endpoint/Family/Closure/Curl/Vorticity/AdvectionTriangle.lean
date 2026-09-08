import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.ProductMass

/-!
# Six-term triangle bound for differentiated endpoint advection

`RHSExpansion` expands one spatial derivative of an advection component into
six products, while `ProductMass` already bounds the compact-test mass of each
of those two product shapes.

This file inserts the purely algebraic bridge between them.  It names the two
products attached to one transport axis and proves that the norm of the full
differentiated advection component is bounded by the sum of the six product
norms.  A weighted version multiplies the inequality by the nonnegative weak
test norm.

No integration or new analytic estimate is performed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- The first-times-first product associated with one transport axis in
`∂ₐ ((u · ∇)uⱼ)`. -/
noncomputable def h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (s : ℝ)
    (a i j : PrimeTensor.Axis Depth.three)
    (x : Point3) : ℝ :=
  spatial3.d
      a
      (loggedVelocityComponent u s i)
      x
    *
  spatial3.d
      i
      (loggedVelocityComponent u s j)
      x

/-- The zeroth-times-second product associated with one transport axis in
`∂ₐ ((u · ∇)uⱼ)`. -/
noncomputable def h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (s : ℝ)
    (a i j : PrimeTensor.Axis Depth.three)
    (x : Point3) : ℝ :=
  loggedVelocityComponent u s i x
    *
  spatial3.d
      a
      (spatial3.d
        i
        (loggedVelocityComponent u s j))
      x

/-- The differentiated advection component is pointwise dominated by the sum
of its six product norms. -/
theorem norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_le_sixProducts
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    ‖spatial3.d
        a
        (fun q =>
          realAdvectionComponent
            (logSpaceTimeVectorField u) s q j)
        x‖
      ≤
    (
      ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
          u s a xAxis j x‖
        +
      ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
          u s a xAxis j x‖
    )
      +
    (
      (
        ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
            u s a yAxis j x‖
          +
        ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
            u s a yAxis j x‖
      )
        +
      (
        ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
            u s a zAxis j x‖
          +
        ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
            u s a zAxis j x‖
      )
    ) := by
  rw [
    h3LoggedPreterminal_spatial_d_realAdvectionComponent
      hNS hs x a j
  ]

  unfold
    h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
    h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
    loggedVelocityComponent

  exact
    (norm_add_le
      (
        spatial3.d
            a
            (fun q =>
              (logSpaceTimeVectorField u s q).component xAxis)
            x
          *
        spatial3.d
            xAxis
            (fun q =>
              (logSpaceTimeVectorField u s q).component j)
            x
        +
        (logSpaceTimeVectorField u s x).component xAxis
          *
        spatial3.d
            a
            (spatial3.d
              xAxis
              (fun q =>
                (logSpaceTimeVectorField u s q).component j))
            x
      )
      (
        (
          spatial3.d
              a
              (fun q =>
                (logSpaceTimeVectorField u s q).component yAxis)
              x
            *
          spatial3.d
              yAxis
              (fun q =>
                (logSpaceTimeVectorField u s q).component j)
              x
          +
          (logSpaceTimeVectorField u s x).component yAxis
            *
          spatial3.d
              a
              (spatial3.d
                yAxis
                (fun q =>
                  (logSpaceTimeVectorField u s q).component j))
              x
        )
          +
        (
          spatial3.d
              a
              (fun q =>
                (logSpaceTimeVectorField u s q).component zAxis)
              x
            *
          spatial3.d
              zAxis
              (fun q =>
                (logSpaceTimeVectorField u s q).component j)
              x
          +
          (logSpaceTimeVectorField u s x).component zAxis
            *
          spatial3.d
              a
              (spatial3.d
                zAxis
                (fun q =>
                  (logSpaceTimeVectorField u s q).component j))
              x
        )
      )).trans
      (add_le_add
        (norm_add_le _ _)
        ((norm_add_le _ _).trans
          (add_le_add
            (norm_add_le _ _)
            (norm_add_le _ _))))

/-- Multiplying by the weak-test norm preserves the six-term pointwise
majorant. -/
theorem weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_le_sixProducts
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ψ : H3WeakTestFunction)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    ‖ψ x‖ *
      ‖spatial3.d
          a
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q j)
          x‖
      ≤
    (
      ‖ψ x‖ *
        ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
            u s a xAxis j x‖
        +
      ‖ψ x‖ *
        ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
            u s a xAxis j x‖
    )
      +
    (
      (
        ‖ψ x‖ *
          ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
              u s a yAxis j x‖
          +
        ‖ψ x‖ *
          ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
              u s a yAxis j x‖
      )
        +
      (
        ‖ψ x‖ *
          ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
              u s a zAxis j x‖
          +
        ‖ψ x‖ *
          ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
              u s a zAxis j x‖
      )
    ) := by
  have h :=
    norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_le_sixProducts
      hNS hs x a j

  have hWeighted :=
    mul_le_mul_of_nonneg_left
      h
      (norm_nonneg (ψ x))

  simpa only [mul_add] using hWeighted

end

end Euclidean
end Bridge
end PrimeTensor
