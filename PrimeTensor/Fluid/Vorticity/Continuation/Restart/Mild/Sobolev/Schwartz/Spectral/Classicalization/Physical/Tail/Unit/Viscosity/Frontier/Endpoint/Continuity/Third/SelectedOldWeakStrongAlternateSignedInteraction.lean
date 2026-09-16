import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongAlternateTransportIntegralBound

/-!
# Alternate weak--strong signed interaction

The alternate split leaves the signed interaction

    Σ_j D_j ((D · ∇)O_j).

The preceding file bounded the corresponding absolute density by

    3 B |D|²

and integrated that bound to

    ∫ absInteraction ≤ 3 B ‖D‖².

This file packages the signed density itself, proves it integrable, and derives

    |∫ signedInteraction|
      ≤
    3 B ‖D‖².

That is the exact scalar estimate needed once the Leray-forcing pairing is
identified with the alternate signed interaction integral.
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

noncomputable local instance axisFintypeH3SelectedOldWeakStrongAlternateSignedInteraction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Signed three-coordinate alternate weak--strong interaction density. -/
noncomputable def selectedOldWeakStrongOldGradientSignedInteractionDensity
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3) : ℝ :=
  selectedOldWeakStrongOldGradientProduct
      selected old s x xAxis
    +
  (
    selectedOldWeakStrongOldGradientProduct
        selected old s x yAxis
      +
    selectedOldWeakStrongOldGradientProduct
        selected old s x zAxis
  )

/-- The signed alternate density is pointwise dominated by the already-defined
absolute alternate density. -/
theorem abs_selectedOldWeakStrongOldGradientSignedInteractionDensity_le
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3) :
    abs
        (selectedOldWeakStrongOldGradientSignedInteractionDensity
          selected old s x)
      ≤
    selectedOldWeakStrongOldGradientAbsInteractionDensity
      selected old s x := by
  let px : ℝ :=
    selectedOldWeakStrongOldGradientProduct
      selected old s x xAxis

  let py : ℝ :=
    selectedOldWeakStrongOldGradientProduct
      selected old s x yAxis

  let pz : ℝ :=
    selectedOldWeakStrongOldGradientProduct
      selected old s x zAxis

  have hxy :
      abs (py + pz) ≤ abs py + abs pz :=
    abs_add_le py pz

  have hx :
      abs (px + (py + pz))
        ≤
      abs px + abs (py + pz) :=
    abs_add_le px (py + pz)

  have hSigned :
      selectedOldWeakStrongOldGradientSignedInteractionDensity
          selected old s x
        =
      px + (py + pz) := by
    rfl

  have hAbs :
      selectedOldWeakStrongOldGradientAbsInteractionDensity
          selected old s x
        =
      abs px + (abs py + abs pz) := by
    rfl

  rw [hSigned, hAbs]

  linarith

/-- The signed alternate interaction density is continuous whenever both
velocity slices are spatially `C¹`. -/
theorem selectedOldWeakStrongOldGradientSignedInteractionDensity_continuous
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
      (selectedOldWeakStrongOldGradientSignedInteractionDensity
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
    selectedOldWeakStrongOldGradientSignedInteractionDensity

  exact
    hx.add (hy.add hz)

/-- The concrete signed alternate interaction density is integrable. -/
theorem h3PreterminalSelectedOldWeakStrongOldGradientSignedInteractionDensity_integrable
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
      (selectedOldWeakStrongOldGradientSignedInteractionDensity
        (h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail)
        (h3PreterminalOldElapsedWeakStrongVelocity u t)
        (q : ℝ))
      (volume : Measure Point3) := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  let signed : Point3 → ℝ :=
    selectedOldWeakStrongOldGradientSignedInteractionDensity
      selected old (q : ℝ)

  let absDensity : Point3 → ℝ :=
    selectedOldWeakStrongOldGradientAbsInteractionDensity
      selected old (q : ℝ)

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

  have hSignedContinuous :
      Continuous signed := by
    dsimp only [signed]

    exact
      selectedOldWeakStrongOldGradientSignedInteractionDensity_continuous
        selected old (q : ℝ) hSelected hOld

  have hSignedMeasurable :
      AEStronglyMeasurable signed
        (volume : Measure Point3) :=
    hSignedContinuous.aestronglyMeasurable

  have hAbs :
      Integrable absDensity
        (volume : Measure Point3) := by
    dsimp only [absDensity, selected, old]

    exact
      h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_integrable
        hNS ht hEnd hE hTail q

  have hDom :
      ∀ x : Point3,
        ‖signed x‖ ≤ absDensity x := by
    intro x

    dsimp only [signed, absDensity]
    rw [Real.norm_eq_abs]

    exact
      abs_selectedOldWeakStrongOldGradientSignedInteractionDensity_le
        selected old (q : ℝ) x

  change
    Integrable signed
      (volume : Measure Point3)

  exact
    hAbs.mono'
      hSignedMeasurable
      (Filter.Eventually.of_forall hDom)

/-- Absolute value of the concrete signed alternate interaction integral is
bounded by the integral of the absolute interaction density. -/
theorem abs_integral_h3PreterminalSelectedOldWeakStrongOldGradientSignedInteractionDensity_le_absDensity
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    abs
      (∫ x : Point3,
        selectedOldWeakStrongOldGradientSignedInteractionDensity
          (h3PreterminalSelectedWeakStrongVelocity
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail)
          (h3PreterminalOldElapsedWeakStrongVelocity u t)
          (q : ℝ)
          x
        ∂volume)
      ≤
    ∫ x : Point3,
      h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity
        hNS ht hE hTail (q : ℝ) x
      ∂volume := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  let signed : Point3 → ℝ :=
    selectedOldWeakStrongOldGradientSignedInteractionDensity
      selected old (q : ℝ)

  let absDensity : Point3 → ℝ :=
    selectedOldWeakStrongOldGradientAbsInteractionDensity
      selected old (q : ℝ)

  have hSigned :
      Integrable signed
        (volume : Measure Point3) := by
    dsimp only [signed, selected, old]

    exact
      h3PreterminalSelectedOldWeakStrongOldGradientSignedInteractionDensity_integrable
        hNS ht hEnd hE hTail q

  have hAbs :
      Integrable absDensity
        (volume : Measure Point3) := by
    dsimp only [absDensity, selected, old]

    exact
      h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_integrable
        hNS ht hEnd hE hTail q

  have hPoint :
      ∀ x : Point3,
        abs (signed x) ≤ absDensity x := by
    intro x
    dsimp only [signed, absDensity]

    exact
      abs_selectedOldWeakStrongOldGradientSignedInteractionDensity_le
        selected old (q : ℝ) x

  have hTriangle :
      abs (∫ x : Point3, signed x ∂volume)
        ≤
      ∫ x : Point3, abs (signed x) ∂volume := by
    simpa only [Real.norm_eq_abs] using
      (abs_integral_le_integral_abs
        (μ := (volume : Measure Point3))
        (f := signed))

  have hMono :
      (∫ x : Point3, abs (signed x) ∂volume)
        ≤
      ∫ x : Point3, absDensity x ∂volume := by
    exact
      integral_mono
        hSigned.abs
        hAbs
        hPoint

  change
    abs (∫ x : Point3, signed x ∂volume)
      ≤
    ∫ x : Point3, absDensity x ∂volume

  exact
    hTriangle.trans hMono

/-- Final scalar alternate interaction estimate:

    |∫ Σ_j D_j ((D · ∇)O_j)|
      ≤
    3 B ‖D‖²,

with the explicit endpoint-independent envelope
`B = h3PreterminalSelectedWeakStrongGradientEnvelope E`. -/
theorem abs_integral_h3PreterminalSelectedOldWeakStrongOldGradientSignedInteractionDensity_le_norm_sq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    abs
      (∫ x : Point3,
        selectedOldWeakStrongOldGradientSignedInteractionDensity
          (h3PreterminalSelectedWeakStrongVelocity
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail)
          (h3PreterminalOldElapsedWeakStrongVelocity u t)
          (q : ℝ)
          x
        ∂volume)
      ≤
    3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q‖ ^ 2 := by
  exact
    (abs_integral_h3PreterminalSelectedOldWeakStrongOldGradientSignedInteractionDensity_le_absDensity
      hNS ht hEnd hE hTail q).trans
      (integral_h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_le_norm_sq
        hNS ht hEnd hE hTail q)

end

end Euclidean
end Bridge
end PrimeTensor
