import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Energy.Reduction
import PrimeTensor.Bridge.Euclidean.Advection.Product

/-!
# Selected--old weak--strong transport split

The diffusion contribution to the concrete selected--old relative-energy
pairing has already been discarded.  The remaining analytic term is the
difference of the quadratic convection/Leray forcing.

This file isolates the pointwise quadratic algebra before introducing the
Leray projector or whole-space integration by parts.

For two classical velocity fields `S` and `O`, write `D = S - O`.  Componentwise,

    (S · ∇)S - (O · ∇)O
      = (D · ∇)S + (O · ∇)D.

The first term is the weak--strong term that will be estimated by the spatial
gradient of the selected branch.  The second term is the skew transport term
that will disappear after pairing with `D` and using incompressibility of the
old branch.

We prove the identity in two stages:

* a purely algebraic split using literal differences of first derivatives;
* a `SpatialC1` bridge identifying those derivative differences with the
  derivative of the selected-minus-old component.

No integration, projection, endpoint continuity, or temporal derivative is
used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongTransportSplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The `((S-O) · ∇)S` component in the weak--strong convection split. -/
noncomputable def realAdvectionSelectedGradientDifferenceComponent
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=
  ((selected t x).component xAxis - (old t x).component xAxis)
      *
    spatial3.d
      xAxis
      (fun y => (selected t y).component j)
      x
    +
  (
    ((selected t x).component yAxis - (old t x).component yAxis)
        *
      spatial3.d
        yAxis
        (fun y => (selected t y).component j)
        x
      +
    ((selected t x).component zAxis - (old t x).component zAxis)
        *
      spatial3.d
        zAxis
        (fun y => (selected t y).component j)
        x
  )

/-- Raw form of the `O · ∇(S-O)` component, written using differences of
first derivatives. -/
noncomputable def realAdvectionOldTransportDifferenceComponentRaw
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=
  (old t x).component xAxis
      *
    (
      spatial3.d
        xAxis
        (fun y => (selected t y).component j)
        x
        -
      spatial3.d
        xAxis
        (fun y => (old t y).component j)
        x
    )
    +
  (
    (old t x).component yAxis
        *
      (
        spatial3.d
          yAxis
          (fun y => (selected t y).component j)
          x
          -
        spatial3.d
          yAxis
          (fun y => (old t y).component j)
          x
      )
      +
    (old t x).component zAxis
        *
      (
        spatial3.d
          zAxis
          (fun y => (selected t y).component j)
          x
          -
        spatial3.d
          zAxis
          (fun y => (old t y).component j)
          x
      )
  )

/-- Actual old-velocity transport of the selected-minus-old component. -/
noncomputable def realAdvectionOldTransportDifferenceComponent
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=
  (old t x).component xAxis
      *
    spatial3.d
      xAxis
      (fun y =>
        (selected t y).component j
          -
        (old t y).component j)
      x
    +
  (
    (old t x).component yAxis
        *
      spatial3.d
        yAxis
        (fun y =>
          (selected t y).component j
            -
          (old t y).component j)
        x
      +
    (old t x).component zAxis
        *
      spatial3.d
        zAxis
        (fun y =>
          (selected t y).component j
            -
          (old t y).component j)
        x
  )

/-- Pure pointwise quadratic algebra:
`(S·∇)S - (O·∇)O = ((S-O)·∇)S + O·(∇S-∇O)`. -/
theorem realAdvectionComponent_sub_eq_selectedGradient_add_oldTransportRaw
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    realAdvectionComponent selected t x j
        -
      realAdvectionComponent old t x j
      =
    realAdvectionSelectedGradientDifferenceComponent
        selected old t x j
      +
    realAdvectionOldTransportDifferenceComponentRaw
        selected old t x j := by
  unfold
    realAdvectionComponent
    realAdvectionSelectedGradientDifferenceComponent
    realAdvectionOldTransportDifferenceComponentRaw
  ring

/-- Under spatial `C¹` regularity, the raw derivative-difference transport term
is exactly `O · ∇(S-O)`. -/
theorem realAdvectionOldTransportDifferenceComponentRaw_eq
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y =>
            (selected t y).component k))
    (hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y =>
            (old t y).component k)) :
    realAdvectionOldTransportDifferenceComponentRaw
        selected old t x j
      =
    realAdvectionOldTransportDifferenceComponent
        selected old t x j := by
  unfold
    realAdvectionOldTransportDifferenceComponentRaw
    realAdvectionOldTransportDifferenceComponent

  rw [
    SpatialC1.spatial3_d_sub
      (hSelected j) (hOld j) x xAxis,
    SpatialC1.spatial3_d_sub
      (hSelected j) (hOld j) x yAxis,
    SpatialC1.spatial3_d_sub
      (hSelected j) (hOld j) x zAxis
  ]

/-- Weak--strong pointwise convection identity:
`(S·∇)S - (O·∇)O = ((S-O)·∇)S + O·∇(S-O)`. -/
theorem realAdvectionComponent_sub_eq_selectedGradient_add_oldTransport
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y =>
            (selected t y).component k))
    (hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y =>
            (old t y).component k)) :
    realAdvectionComponent selected t x j
        -
      realAdvectionComponent old t x j
      =
    realAdvectionSelectedGradientDifferenceComponent
        selected old t x j
      +
    realAdvectionOldTransportDifferenceComponent
        selected old t x j := by
  rw [
    realAdvectionComponent_sub_eq_selectedGradient_add_oldTransportRaw,
    realAdvectionOldTransportDifferenceComponentRaw_eq
      selected old t x j hSelected hOld
  ]

end

end Euclidean
end Bridge
end PrimeTensor
