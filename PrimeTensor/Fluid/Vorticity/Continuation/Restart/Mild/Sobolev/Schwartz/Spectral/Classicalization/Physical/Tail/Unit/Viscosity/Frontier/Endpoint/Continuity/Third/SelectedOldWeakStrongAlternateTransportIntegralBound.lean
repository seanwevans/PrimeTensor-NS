import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongAlternateTransportCancellation

/-!
# Alternate weak--strong interaction: integrated physical L² bound

The alternate convection split leaves

    ((S-O) · ∇)O

after the selected pure-transport piece is cancelled.  The preceding algebraic
increment proved the pointwise estimate

    Σ_j |D_j ((D · ∇)O_j)|
      ≤ 3 B |D|²,

with the explicit endpoint-independent old-gradient envelope

    B = C₁ (2E).

This file closes the analytic bookkeeping around that estimate:

* the alternate interaction coordinates are continuous;
* the absolute three-coordinate interaction density is continuous;
* domination by the concrete selected-minus-old square density makes it
  integrable;
* integrating the pointwise bound and using the existing square-density/L²
  bridge gives

      ∫ alternateInteraction ≤ 3 B ‖D‖².

No transport cancellation or temporal derivative is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongTransportIntegralBound

noncomputable local instance axisFintypeH3SelectedOldWeakStrongAlternateTransportIntegralBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One alternate old-gradient interaction coordinate is continuous whenever
both velocity slices are spatially `C¹`. -/
theorem selectedOldWeakStrongOldGradientProduct_continuous
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (j : PrimeTensor.Axis Depth.three)
    (hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected s x).component k))
    (hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old s x).component k)) :
    Continuous
      (selectedOldWeakStrongOldGradientProduct
        selected old s · j) := by
  have hDifference
      (k : PrimeTensor.Axis Depth.three) :
      Continuous
        (fun x : Point3 =>
          (selected s x).component k
            -
          (old s x).component k) :=
    (hSelected k).continuous.sub (hOld k).continuous

  have hDerivative
      (a : PrimeTensor.Axis Depth.three) :
      Continuous
        (spatial3.d
          a
          (fun y : Point3 =>
            (old s y).component j)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      (hOld j) a

  unfold
    selectedOldWeakStrongOldGradientProduct
    realAdvectionOldGradientDifferenceComponent

  exact
    (hDifference j).mul
      (((hDifference xAxis).mul (hDerivative xAxis)).add
        (((hDifference yAxis).mul (hDerivative yAxis)).add
          ((hDifference zAxis).mul (hDerivative zAxis))))

/-- The full absolute alternate interaction density is continuous. -/
theorem selectedOldWeakStrongOldGradientAbsInteractionDensity_continuous
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected s x).component k))
    (hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old s x).component k)) :
    Continuous
      (selectedOldWeakStrongOldGradientAbsInteractionDensity
        selected old s) := by
  have hx :=
    selectedOldWeakStrongOldGradientProduct_continuous
      selected old s xAxis hSelected hOld

  have hy :=
    selectedOldWeakStrongOldGradientProduct_continuous
      selected old s yAxis hSelected hOld

  have hz :=
    selectedOldWeakStrongOldGradientProduct_continuous
      selected old s zAxis hSelected hOld

  unfold
    selectedOldWeakStrongOldGradientAbsInteractionDensity

  exact
    hx.abs.add (hy.abs.add hz.abs)

/-- Concrete alternate absolute interaction density for the actual selected
restart and old elapsed branch. -/
noncomputable def h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (s : ℝ)
    (x : Point3) : ℝ :=
  selectedOldWeakStrongOldGradientAbsInteractionDensity
    (h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail)
    (h3PreterminalOldElapsedWeakStrongVelocity u t)
    s x

/-- The concrete alternate absolute interaction density is continuous at each
closed elapsed time. -/
theorem h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_continuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    Continuous
      (h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity
        hNS ht hE hTail (q : ℝ)) := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  have hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected (q : ℝ) x).component k) := by
    intro k
    dsimp only [selected]

    exact
      h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) k

  have hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old (q : ℝ) x).component k) := by
    intro k
    dsimp only [old]

    exact
      h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
        hNS ht hEnd hTail q k

  change
    Continuous
      (selectedOldWeakStrongOldGradientAbsInteractionDensity
        selected old (q : ℝ))

  exact
    selectedOldWeakStrongOldGradientAbsInteractionDensity_continuous
      selected old (q : ℝ) hSelected hOld

/-- The concrete alternate absolute interaction density is automatically
integrable by domination by the selected-minus-old `L²` square density. -/
theorem h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    Integrable
      (h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity
        hNS ht hE hTail (q : ℝ))
      (volume : Measure Point3) := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  let B :=
    h3PreterminalSelectedWeakStrongGradientEnvelope E

  let square : Point3 → ℝ :=
    selectedOldVelocityDifferenceSquarePointwise
      selected old (q : ℝ)

  let interaction : Point3 → ℝ :=
    selectedOldWeakStrongOldGradientAbsInteractionDensity
      selected old (q : ℝ)

  let majorant : Point3 → ℝ :=
    fun x => 3 * B * square x

  have hSquare :
      Integrable square
        (volume : Measure Point3) := by
    dsimp only [square, selected, old]

    exact
      selectedOldVelocityDifferenceSquarePointwise_actual_integrable
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q

  have hMajorant :
      Integrable majorant
        (volume : Measure Point3) := by
    dsimp only [majorant]

    exact
      hSquare.const_mul (3 * B)

  have hContinuous :
      Continuous interaction := by
    dsimp only [interaction, selected, old]

    exact
      h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_continuous
        hNS ht hEnd hE hTail q

  have hMeasurable :
      AEStronglyMeasurable interaction
        (volume : Measure Point3) :=
    hContinuous.aestronglyMeasurable

  have hDom :
      ∀ x : Point3,
        ‖interaction x‖ ≤ majorant x := by
    intro x

    have hPoint :
        interaction x ≤ majorant x := by
      dsimp only [interaction, majorant, square, B]

      exact
        h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_le
          hNS ht hEnd hE hTail q x

    have hNonneg :
        0 ≤ interaction x := by
      dsimp only [interaction]
      unfold
        selectedOldWeakStrongOldGradientAbsInteractionDensity
      positivity

    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]

    exact hPoint

  change
    Integrable interaction
      (volume : Measure Point3)

  exact
    hMajorant.mono'
      hMeasurable
      (Filter.Eventually.of_forall hDom)

/-- Integrated alternate weak--strong estimate in the exact physical `L²`
norm language required by the relative-energy argument. -/
theorem integral_h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_le_norm_sq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ x : Point3,
      h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity
        hNS ht hE hTail (q : ℝ) x
      ∂volume)
      ≤
    3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q‖ ^ 2 := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  let B :=
    h3PreterminalSelectedWeakStrongGradientEnvelope E

  let square : Point3 → ℝ :=
    selectedOldVelocityDifferenceSquarePointwise
      selected old (q : ℝ)

  let interaction : Point3 → ℝ :=
    selectedOldWeakStrongOldGradientAbsInteractionDensity
      selected old (q : ℝ)

  let majorant : Point3 → ℝ :=
    fun x => 3 * B * square x

  have hInteraction :
      Integrable interaction
        (volume : Measure Point3) := by
    dsimp only [interaction, selected, old]

    exact
      h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_integrable
        hNS ht hEnd hE hTail q

  have hSquare :
      Integrable square
        (volume : Measure Point3) := by
    dsimp only [square, selected, old]

    exact
      selectedOldVelocityDifferenceSquarePointwise_actual_integrable
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q

  have hMajorant :
      Integrable majorant
        (volume : Measure Point3) := by
    dsimp only [majorant]

    exact
      hSquare.const_mul (3 * B)

  have hPoint :
      ∀ x : Point3,
        interaction x ≤ majorant x := by
    intro x
    dsimp only [interaction, majorant, square, B]

    exact
      h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_le
        hNS ht hEnd hE hTail q x

  have hIntegral :
      (∫ x : Point3, interaction x ∂volume)
        ≤
      ∫ x : Point3, majorant x ∂volume := by
    exact
      integral_mono
        hInteraction
        hMajorant
        hPoint

  have hMajorantIntegral :
      (∫ x : Point3, majorant x ∂volume)
        =
      3 * B *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q‖ ^ 2 := by
    dsimp only [majorant]

    rw [
      integral_const_mul
    ]

    dsimp only [square, selected, old]

    rw [
      selectedOldVelocityDifferenceSquarePointwise_actual_eq
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q,
      integral_h3PreterminalSelectedOldVelocitySquareDensity_eq_norm_sq
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
    ]

  change
    (∫ x : Point3, interaction x ∂volume)
      ≤
    3 * B *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q‖ ^ 2

  rw [← hMajorantIntegral]

  exact hIntegral

end

end Euclidean
end Bridge
end PrimeTensor
