import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Weak.Schwartz
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Compact.Density

/-!
# Ordered-third endpoint continuity: reduce weak H³ continuity to smooth compact tests

`WeakSchwartz` reduced the weak H³ problem to a dense smooth test class.
For the next Fourier/physical bridge it is more convenient to use the stronger
density theorem already available in `Spectral.Compact.Density`:

smooth compactly-supported representatives are dense in the exact weighted
spectral `L²` state.

For a smooth compact weighted test `g`, multiplication by the exact H³ weight
preserves compact support and smoothness.  Thus the next file can move the
weight from the old encoded state onto the fixed test without proving any
global weighted-Schwartz multiplier theorem.

This file contains only the density extension.  A uniformly H³-bounded path
whose weak real pairings are continuous against every smooth compact weighted
spectral test is weakly continuous against every spectral `L²` test.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  ComplexConjugate ContDiff

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityThirdWeakCompact
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Predicate selecting the dense smooth compact subspace of the weighted
spectral scalar state. -/
def H3SpectralScalarHasSmoothCompactRepresentative
    (F : H3SpectralScalarState) : Prop :=
  ∃ g : H3FourierPoint3 → ℂ,
    (F : H3FourierPoint3 → ℂ) =ᵐ[volume] g
      ∧
    HasCompactSupport g
      ∧
    ContDiff ℝ ∞ g

/-- Smooth compact weighted spectral test-pairing continuity. -/
def H3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀
    (j : Fin 3)
    (F : H3SpectralScalarState),
      H3SpectralScalarHasSmoothCompactRepresentative F
        →
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          (inner ℂ
            (h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q j)
            F).re)

/-- Generic density extension from smooth compact spectral tests to arbitrary
spectral tests for a uniformly bounded path. -/
theorem continuous_re_inner_of_smoothCompact_of_uniform_bound
    {α : Type*}
    [PseudoMetricSpace α]
    (F : α → H3SpectralScalarState)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hBound : ∀ q : α, ‖F q‖ ≤ B)
    (hCompact :
      ∀ G : H3SpectralScalarState,
        H3SpectralScalarHasSmoothCompactRepresentative G
          →
        Continuous
          (fun q : α =>
            (inner ℂ (F q) G).re))
    (Φ : H3SpectralScalarState) :
    Continuous
      (fun q : α =>
        (inner ℂ (F q) Φ).re) := by
  rw [continuous_iff_continuousAt]
  intro q₀

  rw [Metric.continuousAt_iff]
  intro ε hε

  have hB1 :
      0 < B + 1 := by
    linarith

  let η : ℝ :=
    ε / (4 * (B + 1))

  have hη :
      0 < η := by
    dsimp only [η]
    positivity

  obtain ⟨G, hGrep, hGclose⟩ :=
    exists_h3SmoothCompact_spectralApprox_norm
      Φ hη

  have hApprox :
      ∀ q : α,
        dist
            (inner ℂ (F q) Φ).re
            (inner ℂ (F q) G).re
          <
        ε / 4 := by
    intro q

    have hPair :=
      dist_re_inner_right_le_norm_mul_norm_sub
        (F q) Φ G

    have hNormMul :
        ‖F q‖ * ‖Φ - G‖
          ≤
        B * ‖Φ - G‖ := by
      exact
        mul_le_mul_of_nonneg_right
          (hBound q)
          (norm_nonneg (Φ - G))

    have hBLe :
        B ≤ B + 1 := by
      linarith

    have hBPlus :
        B * ‖Φ - G‖
          ≤
        (B + 1) * ‖Φ - G‖ := by
      exact
        mul_le_mul_of_nonneg_right
          hBLe
          (norm_nonneg (Φ - G))

    have hApproxMul :
        (B + 1) * ‖Φ - G‖
          <
        (B + 1) * η := by
      exact
        mul_lt_mul_of_pos_left
          hGclose
          hB1

    have hEtaEq :
        (B + 1) * η
          =
        ε / 4 := by
      dsimp only [η]
      field_simp

    exact
      lt_of_le_of_lt
        hPair
        (lt_of_le_of_lt
          hNormMul
          (lt_of_le_of_lt
            hBPlus
            (by
              rw [hEtaEq] at hApproxMul
              exact hApproxMul)))

  have hGCont :
      Continuous
        (fun q : α =>
          (inner ℂ (F q) G).re) :=
    hCompact G hGrep

  have hGAt :=
    Metric.continuousAt_iff.mp
      (hGCont.continuousAt (x := q₀))
      (ε / 2)
      (by linarith)

  obtain ⟨δ, hδ, hδprop⟩ :=
    hGAt

  refine ⟨δ, hδ, ?_⟩
  intro q hq

  have hMid :
      dist
          (inner ℂ (F q) G).re
          (inner ℂ (F q₀) G).re
        <
      ε / 2 :=
    hδprop hq

  have hLeft :
      dist
          (inner ℂ (F q) Φ).re
          (inner ℂ (F q) G).re
        <
      ε / 4 :=
    hApprox q

  have hRight :
      dist
          (inner ℂ (F q₀) G).re
          (inner ℂ (F q₀) Φ).re
        <
      ε / 4 := by
    rw [dist_comm]
    exact hApprox q₀

  calc
    dist
        (inner ℂ (F q) Φ).re
        (inner ℂ (F q₀) Φ).re
        ≤
      dist
          (inner ℂ (F q) Φ).re
          (inner ℂ (F q) G).re
        +
      dist
          (inner ℂ (F q) G).re
          (inner ℂ (F q₀) Φ).re :=
      dist_triangle _ _ _
    _ ≤
      dist
          (inner ℂ (F q) Φ).re
          (inner ℂ (F q) G).re
        +
      (dist
          (inner ℂ (F q) G).re
          (inner ℂ (F q₀) G).re
        +
       dist
          (inner ℂ (F q₀) G).re
          (inner ℂ (F q₀) Φ).re) := by
      have hTri :
          dist
              (inner ℂ (F q) G).re
              (inner ℂ (F q₀) Φ).re
            ≤
          dist
              (inner ℂ (F q) G).re
              (inner ℂ (F q₀) G).re
            +
          dist
              (inner ℂ (F q₀) G).re
              (inner ℂ (F q₀) Φ).re :=
        dist_triangle _ _ _
      linarith
    _ <
      ε / 4 + (ε / 2 + ε / 4) := by
      exact
        add_lt_add
          hLeft
          (add_lt_add hMid hRight)
    _ = ε := by
      ring

/-- Smooth compact weak continuity extends to arbitrary spectral weak
continuity using the retained uniform H³ tail bound. -/
theorem h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_of_smoothCompact
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hCompact :
      H3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralWeakContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j Φ

  let Uj :
      Set.Icc (0 : ℝ) tau →
        H3SpectralScalarState :=
    fun q =>
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q j

  have hTwoE :
      0 ≤ 2 * E := by
    linarith

  have hBound :
      ∀ q : Set.Icc (0 : ℝ) tau,
        ‖Uj q‖ ≤ 2 * E := by
    intro q

    exact
      (h3SpectralVelocity_coordinate_norm_le
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        j).trans
        (norm_h3PreterminalTailCanonicalSpectralStateOnElapsed_le_twoE
          hNS ht hEnd hE hTail q)

  exact
    continuous_re_inner_of_smoothCompact_of_uniform_bound
      Uj
      (2 * E)
      hTwoE
      hBound
      (hCompact j)
      Φ

/-- Local weak-plus-norm package from smooth compact weak tests plus
coordinate-norm continuity. -/
theorem h3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed_of_smoothCompact_of_norm
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hCompact :
      H3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed
        hNS ht hEnd hTail)
    (hNorm :
      H3PreterminalCanonicalSpectralCoordinateNormContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    ⟨
      h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_of_smoothCompact
        hNS ht hEnd hE hTail hCompact,
      hNorm
    ⟩

/-- Restart-radius frontier with smooth compact weak tests plus scalar
spectral-coordinate norm continuity. -/
def H3PreterminalTailUnitViscositySpectralSmoothCompactWeakNormContinuityFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        H3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed
            hNS ht hEnd hTail
          ∧
        H3PreterminalCanonicalSpectralCoordinateNormContinuousOnElapsed
            hNS ht hEnd hTail

/-- Radius-wide smooth compact weak plus norm continuity implies the existing
weak-plus-norm frontier. -/
theorem h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius_of_smoothCompact
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hCompact :
      H3PreterminalTailUnitViscositySpectralSmoothCompactWeakNormContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  have hLocal :=
    hCompact q hqPos hEnd

  exact
    h3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed_of_smoothCompact_of_norm
      hNS ht hEnd hE hTail
      hLocal.1
      hLocal.2

/-- Global smooth-compact weak plus coordinate-norm continuity frontier. -/
def H3PreterminalTailUnitViscositySpectralSmoothCompactWeakNormContinuityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscositySpectralSmoothCompactWeakNormContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- Global smooth compact weak plus norm continuity closes the global
weak-plus-norm frontier. -/
theorem h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier_of_smoothCompact
    (hCompact :
      H3PreterminalTailUnitViscositySpectralSmoothCompactWeakNormContinuityFrontier) :
    H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier := by
  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius_of_smoothCompact
      hNS ht hE hTail
      (hCompact E hE u T t hNS ht hTail)

/-- Current continuation theorem with the third branch reduced to smooth
compact weighted weak tests plus scalar spectral-coordinate norm continuity. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralSmoothCompactWeakNormClosed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hCompact :
      H3PreterminalTailUnitViscositySpectralSmoothCompactWeakNormContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralWeakNormClosed
      hOld
      (h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier_of_smoothCompact
        hCompact)

end

end Euclidean
end Bridge
end PrimeTensor
