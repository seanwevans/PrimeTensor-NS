import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongOldGradientEnvelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongTransportVectorBound

/-!
# Alternate selected--old weak--strong transport split

The original relative-energy split used

    (S · ∇)S - (O · ∇)O
      =
    ((S-O) · ∇)S + O · ∇(S-O),

which leaves the selected gradient in the estimated term and asks the old
branch to provide the pure-transport whole-space cancellation.

For the endpoint argument the symmetric decomposition is better:

    (S · ∇)S - (O · ∇)O
      =
    S · ∇(S-O) + ((S-O) · ∇)O.

Now the pure transport is carried by the selected restart branch, while the
surviving weak--strong term only needs the old gradient.  The preceding file
proved exactly the required endpoint-independent old-gradient envelope.

This file performs the algebra and the pointwise quadratic estimate.  No
whole-space cancellation is used yet.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongAlternateTransportSplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The surviving alternate weak--strong term `((S-O) · ∇)O_j`. -/
noncomputable def realAdvectionOldGradientDifferenceComponent
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=
  ((selected t x).component xAxis - (old t x).component xAxis)
      *
    spatial3.d
      xAxis
      (fun y => (old t y).component j)
      x
    +
  (
    ((selected t x).component yAxis - (old t x).component yAxis)
        *
      spatial3.d
        yAxis
        (fun y => (old t y).component j)
        x
      +
    ((selected t x).component zAxis - (old t x).component zAxis)
        *
      spatial3.d
        zAxis
        (fun y => (old t y).component j)
        x
  )

/-- Raw selected transport `S · (∇S_j - ∇O_j)`. -/
noncomputable def realAdvectionSelectedTransportDifferenceComponentRaw
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=
  (selected t x).component xAxis
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
    (selected t x).component yAxis
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
    (selected t x).component zAxis
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

/-- Actual selected transport `S · ∇(S_j-O_j)`. -/
noncomputable def realAdvectionSelectedTransportDifferenceComponent
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=
  (selected t x).component xAxis
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
    (selected t x).component yAxis
        *
      spatial3.d
        yAxis
        (fun y =>
          (selected t y).component j
            -
          (old t y).component j)
        x
      +
    (selected t x).component zAxis
        *
      spatial3.d
        zAxis
        (fun y =>
          (selected t y).component j
            -
          (old t y).component j)
        x
  )

/-- Pure pointwise quadratic algebra for the alternate split. -/
theorem realAdvectionComponent_sub_eq_selectedTransportRaw_add_oldGradient
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    realAdvectionComponent selected t x j
        -
      realAdvectionComponent old t x j
      =
    realAdvectionSelectedTransportDifferenceComponentRaw
        selected old t x j
      +
    realAdvectionOldGradientDifferenceComponent
        selected old t x j := by
  unfold
    realAdvectionComponent
    realAdvectionSelectedTransportDifferenceComponentRaw
    realAdvectionOldGradientDifferenceComponent
  ring

/-- Spatial `C¹` converts the raw derivative difference into the derivative of
the selected-minus-old component. -/
theorem realAdvectionSelectedTransportDifferenceComponentRaw_eq
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y => (selected t y).component k))
    (hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y => (old t y).component k)) :
    realAdvectionSelectedTransportDifferenceComponentRaw
        selected old t x j
      =
    realAdvectionSelectedTransportDifferenceComponent
        selected old t x j := by
  unfold
    realAdvectionSelectedTransportDifferenceComponentRaw
    realAdvectionSelectedTransportDifferenceComponent

  rw [
    SpatialC1.spatial3_d_sub
      (hSelected j) (hOld j) x xAxis,
    SpatialC1.spatial3_d_sub
      (hSelected j) (hOld j) x yAxis,
    SpatialC1.spatial3_d_sub
      (hSelected j) (hOld j) x zAxis
  ]

/-- Alternate weak--strong convection identity:
`(S·∇)S - (O·∇)O = S·∇(S-O) + ((S-O)·∇)O`. -/
theorem realAdvectionComponent_sub_eq_selectedTransport_add_oldGradient
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y => (selected t y).component k))
    (hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y => (old t y).component k)) :
    realAdvectionComponent selected t x j
        -
      realAdvectionComponent old t x j
      =
    realAdvectionSelectedTransportDifferenceComponent
        selected old t x j
      +
    realAdvectionOldGradientDifferenceComponent
        selected old t x j := by
  rw [
    realAdvectionComponent_sub_eq_selectedTransportRaw_add_oldGradient,
    realAdvectionSelectedTransportDifferenceComponentRaw_eq
      selected old t x j hSelected hOld
  ]

/-- The selected pure-transport term is exactly generic scalar transport of
the difference component. -/
theorem realAdvectionSelectedTransportDifferenceComponent_eq_scalarTransport
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    (fun x : Point3 =>
      realAdvectionSelectedTransportDifferenceComponent
        selected old t x j)
      =
    h3ScalarTransport
      selected t
      (selectedOldVelocityDifferenceComponent
        selected old t j) := by
  funext x
  unfold
    realAdvectionSelectedTransportDifferenceComponent
    h3ScalarTransport
    selectedOldVelocityDifferenceComponent
  rfl

/-- One alternate surviving interaction coordinate
`D_j ((D · ∇)O_j)`. -/
noncomputable def selectedOldWeakStrongOldGradientProduct
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=
  ((selected t x).component j - (old t x).component j)
    *
  realAdvectionOldGradientDifferenceComponent
    selected old t x j

/-- A uniform coordinate-gradient bound on the old `j` component controls the
alternate surviving interaction. -/
theorem abs_realAdvectionOldGradientDifferenceComponent_le
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hx :
      abs
        (spatial3.d
          xAxis
          (fun y => (old t y).component j)
          x)
        ≤ B)
    (hy :
      abs
        (spatial3.d
          yAxis
          (fun y => (old t y).component j)
          x)
        ≤ B)
    (hz :
      abs
        (spatial3.d
          zAxis
          (fun y => (old t y).component j)
          x)
        ≤ B) :
    abs
        (realAdvectionOldGradientDifferenceComponent
          selected old t x j)
      ≤
    B *
      selectedOldVelocityDifferenceL1Pointwise
        selected old t x := by
  unfold
    realAdvectionOldGradientDifferenceComponent
    selectedOldVelocityDifferenceL1Pointwise

  exact
    abs_threeTermDot_le_commonBound
      ((selected t x).component xAxis - (old t x).component xAxis)
      ((selected t x).component yAxis - (old t x).component yAxis)
      ((selected t x).component zAxis - (old t x).component zAxis)
      (spatial3.d
        xAxis
        (fun y => (old t y).component j)
        x)
      (spatial3.d
        yAxis
        (fun y => (old t y).component j)
        x)
      (spatial3.d
        zAxis
        (fun y => (old t y).component j)
        x)
      B hB hx hy hz

/-- Pointwise relative-energy density estimate for one alternate surviving
component. -/
theorem abs_selectedOldWeakStrongOldGradientProduct_le
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hx :
      abs
        (spatial3.d
          xAxis
          (fun y => (old t y).component j)
          x)
        ≤ B)
    (hy :
      abs
        (spatial3.d
          yAxis
          (fun y => (old t y).component j)
          x)
        ≤ B)
    (hz :
      abs
        (spatial3.d
          zAxis
          (fun y => (old t y).component j)
          x)
        ≤ B) :
    abs
        (selectedOldWeakStrongOldGradientProduct
          selected old t x j)
      ≤
    B
      *
    abs ((selected t x).component j - (old t x).component j)
      *
    selectedOldVelocityDifferenceL1Pointwise
      selected old t x := by
  unfold selectedOldWeakStrongOldGradientProduct
  rw [abs_mul]

  have hInteraction :=
    abs_realAdvectionOldGradientDifferenceComponent_le
      selected old t x j B hB hx hy hz

  calc
    abs ((selected t x).component j - (old t x).component j)
        *
      abs
        (realAdvectionOldGradientDifferenceComponent
          selected old t x j)
        ≤
      abs ((selected t x).component j - (old t x).component j)
        *
      (B *
        selectedOldVelocityDifferenceL1Pointwise
          selected old t x) := by
        exact
          mul_le_mul_of_nonneg_left
            hInteraction
            (abs_nonneg _)
    _ =
      B
        *
      abs ((selected t x).component j - (old t x).component j)
        *
      selectedOldVelocityDifferenceL1Pointwise
        selected old t x := by
      ring

/-- Sum of the three absolute alternate surviving interactions. -/
noncomputable def selectedOldWeakStrongOldGradientAbsInteractionDensity
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3) : ℝ :=
  abs
      (selectedOldWeakStrongOldGradientProduct
        selected old t x xAxis)
    +
  (
    abs
        (selectedOldWeakStrongOldGradientProduct
          selected old t x yAxis)
      +
    abs
        (selectedOldWeakStrongOldGradientProduct
          selected old t x zAxis)
  )

/-- The alternate surviving density has the same `3 B |D|²` bound as the
original selected-gradient split. -/
theorem selectedOldWeakStrongOldGradientAbsInteractionDensity_le
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hGradient :
      ∀ j i : PrimeTensor.Axis Depth.three,
        abs
          (spatial3.d
            i
            (fun y => (old t y).component j)
            x)
          ≤ B) :
    selectedOldWeakStrongOldGradientAbsInteractionDensity
        selected old t x
      ≤
    3 * B *
      selectedOldVelocityDifferenceSquarePointwise
        selected old t x := by
  have hx :=
    abs_selectedOldWeakStrongOldGradientProduct_le
      selected old t x xAxis B hB
      (hGradient xAxis xAxis)
      (hGradient xAxis yAxis)
      (hGradient xAxis zAxis)

  have hy :=
    abs_selectedOldWeakStrongOldGradientProduct_le
      selected old t x yAxis B hB
      (hGradient yAxis xAxis)
      (hGradient yAxis yAxis)
      (hGradient yAxis zAxis)

  have hz :=
    abs_selectedOldWeakStrongOldGradientProduct_le
      selected old t x zAxis B hB
      (hGradient zAxis xAxis)
      (hGradient zAxis yAxis)
      (hGradient zAxis zAxis)

  have hSum :
      selectedOldWeakStrongOldGradientAbsInteractionDensity
          selected old t x
        ≤
      B
          *
        abs ((selected t x).component xAxis - (old t x).component xAxis)
          *
        selectedOldVelocityDifferenceL1Pointwise
          selected old t x
        +
      (
        B
            *
          abs ((selected t x).component yAxis - (old t x).component yAxis)
            *
          selectedOldVelocityDifferenceL1Pointwise
            selected old t x
          +
        B
            *
          abs ((selected t x).component zAxis - (old t x).component zAxis)
            *
          selectedOldVelocityDifferenceL1Pointwise
            selected old t x
      ) := by
    unfold selectedOldWeakStrongOldGradientAbsInteractionDensity
    exact add_le_add hx (add_le_add hy hz)

  calc
    selectedOldWeakStrongOldGradientAbsInteractionDensity
        selected old t x
        ≤
      B
          *
        abs ((selected t x).component xAxis - (old t x).component xAxis)
          *
        selectedOldVelocityDifferenceL1Pointwise
          selected old t x
        +
      (
        B
            *
          abs ((selected t x).component yAxis - (old t x).component yAxis)
            *
          selectedOldVelocityDifferenceL1Pointwise
            selected old t x
          +
        B
            *
          abs ((selected t x).component zAxis - (old t x).component zAxis)
            *
          selectedOldVelocityDifferenceL1Pointwise
            selected old t x
      ) := hSum
    _ =
      B *
        (selectedOldVelocityDifferenceL1Pointwise
          selected old t x) ^ 2 := by
      unfold selectedOldVelocityDifferenceL1Pointwise
      ring
    _ ≤
      3 * B *
        selectedOldVelocityDifferenceSquarePointwise
          selected old t x := by
      unfold
        selectedOldVelocityDifferenceL1Pointwise
        selectedOldVelocityDifferenceSquarePointwise

      exact
        mul_abs_sum_three_sq_le_three_mul_sum_sq
          ((selected t x).component xAxis - (old t x).component xAxis)
          ((selected t x).component yAxis - (old t x).component yAxis)
          ((selected t x).component zAxis - (old t x).component zAxis)
          B hB

/-- Concrete endpoint-independent version of the alternate pointwise estimate
using the old-gradient envelope proved in the preceding increment. -/
theorem h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (x : Point3) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity
        u t
    selectedOldWeakStrongOldGradientAbsInteractionDensity
        selected old (q : ℝ) x
      ≤
    3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      selectedOldVelocityDifferenceSquarePointwise
        selected old (q : ℝ) x := by
  dsimp only

  apply
    selectedOldWeakStrongOldGradientAbsInteractionDensity_le
      (h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail)
      (h3PreterminalOldElapsedWeakStrongVelocity u t)
      (q : ℝ)
      x
      (h3PreterminalSelectedWeakStrongGradientEnvelope E)
      (h3PreterminalSelectedWeakStrongGradientEnvelope_nonneg hE)

  intro j i

  exact
    h3PreterminalOldElapsedWeakStrongVelocity_spatial_d_le_gradientEnvelope
      hNS ht hEnd hE hTail q x j i

end

end Euclidean
end Bridge
end PrimeTensor
