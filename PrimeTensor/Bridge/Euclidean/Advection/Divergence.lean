import PrimeTensor.Bridge.Euclidean.Advection.Product

/-!
# Euclidean outer-product divergence and advection

The spectral mild equation uses the divergence of the velocity outer product,
while the concrete real Navier--Stokes interface is written with advection

    (u · ∇)u.

For a spatially `C¹` velocity slice, the ordinary product rule gives the exact
coordinate identity

    div(u ⊗ u)_j = (u · ∇)u_j + u_j div u.

Consequently an incompressible velocity has pointwise outer-product divergence
equal to advection.  This file isolates that finite-dimensional Euclidean
calculus fact from the later Fourier reconstruction and Leray-complement
arguments.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

/-- The `j`-component of the ordinary Euclidean divergence of the tensor
`u ⊗ u`, written in the same positive-axis fold convention used by
`RealFluid.advection` and `RealFluid.divergence`. -/
noncomputable def realOuterProductDivergenceComponent
    (u : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=
  PrimeTensor.Axis.fold
    (· + ·)
    Depth.three
    (fun i =>
      spatial3.d
        i
        (fun y =>
          (u t y).component j *
            (u t y).component i)
        x)

/-- Product-rule decomposition of the physical outer-product divergence.

The first term is exactly the project's `RealFluid.advection`; the second is
the output velocity component multiplied by the ordinary divergence. -/
theorem realOuterProductDivergenceComponent_eq_advection_add_component_mul_divergence
    (u : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (hC1 :
      ∀ i : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y : Point3 =>
            (u t y).component i)) :
    realOuterProductDivergenceComponent u t x j
      =
    (PrimeTensor.Bridge.RealFluid.advection
        spatial3 u t x).component j
      +
    (u t x).component j *
      PrimeTensor.Bridge.RealFluid.divergence
        spatial3 (u t) x := by
  have hAdvection :
      (PrimeTensor.Bridge.RealFluid.advection
          spatial3 u t x).component j
        =
      (u t x).component xAxis *
          spatial3.d
            xAxis
            (fun y => (u t y).component j)
            x
        +
      (
        (u t x).component yAxis *
            spatial3.d
              yAxis
              (fun y => (u t y).component j)
              x
          +
        (u t x).component zAxis *
            spatial3.d
              zAxis
              (fun y => (u t y).component j)
              x
      ) := by
    rfl

  have hDivergence :
      PrimeTensor.Bridge.RealFluid.divergence
          spatial3 (u t) x
        =
      spatial3.d
          xAxis
          (fun y => (u t y).component xAxis)
          x
        +
      (
        spatial3.d
            yAxis
            (fun y => (u t y).component yAxis)
            x
          +
        spatial3.d
            zAxis
            (fun y => (u t y).component zAxis)
            x
      ) := by
    rfl

  unfold realOuterProductDivergenceComponent

  rw [
    axis_fold_three,
    SpatialC1.spatial3_d_mul
      (hC1 j) (hC1 xAxis) x xAxis,
    SpatialC1.spatial3_d_mul
      (hC1 j) (hC1 yAxis) x yAxis,
    SpatialC1.spatial3_d_mul
      (hC1 j) (hC1 zAxis) x zAxis,
    hAdvection,
    hDivergence
  ]

  ring

/-- For an incompressible spatially `C¹` velocity slice, divergence of the
physical outer product is exactly the advection term used by the real
Navier--Stokes momentum equation. -/
theorem realOuterProductDivergenceComponent_eq_advection_of_divergence_eq_zero
    (u : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (hC1 :
      ∀ i : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y : Point3 =>
            (u t y).component i))
    (hDiv :
      PrimeTensor.Bridge.RealFluid.divergence
          spatial3 (u t) x
        =
      0) :
    realOuterProductDivergenceComponent u t x j
      =
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3 u t x).component j := by
  rw [
    realOuterProductDivergenceComponent_eq_advection_add_component_mul_divergence
      u t x j hC1,
    hDiv,
    mul_zero,
    add_zero
  ]

end

end Euclidean
end Bridge
end PrimeTensor
