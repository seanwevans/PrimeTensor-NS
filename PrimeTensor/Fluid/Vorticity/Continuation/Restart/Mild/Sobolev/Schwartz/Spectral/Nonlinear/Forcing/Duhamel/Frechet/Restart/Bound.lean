import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Physical.Restart.Radius.Closure

/-!
# Canonical-restart specialization of the nonlinear Duhamel Fréchet bound

The generic full-space Fréchet estimate is now specialized to the actual
Banach-selected path at the canonical restart radius.

The selected normalized path stays in the `2A` ball.  Its canonical physical
extension is therefore globally continuous and globally bounded by `2A`.
Consequently, throughout the genuine restart window `0 ≤ t ≤ R(ν,A)`, the
spatial derivative of the nonlinear Duhamel reconstruction obeys the explicit
quadratic estimate obtained by substituting

    MU = MV = 2A

into the generic bound.

The final theorem states the estimate at the complete canonical restart radius.
This exposes the precise nonlinear spatial-derivative size attached to one
Banach-selected restart step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingDuhamelFrechetRestartBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical physical extension of the Banach-selected restart path is
continuous on all real times. -/
theorem continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    Continuous
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀) := by
  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
  unfold h3SpectralFinHeatLerayMildSolutionPhysicalExtension
  exact
    continuous_h3PathPhysicalRealExtension
      (h3FinHeatLerayRestartRadius ν A)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius
        hν U₀ hA hU₀)

/-- The canonical physical extension remains globally in the same `2A`
Banach ball as the normalized selected path. -/
theorem norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (s : ℝ) :
    ‖h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s‖
      ≤ 2 * A := by
  change
    ‖h3SpectralFinHeatLerayMildSolutionAtRestartRadius
        hν U₀ hA hU₀
        (h3ClampUnitTime
          (s / h3FinHeatLerayRestartRadius ν A))‖
      ≤ 2 * A
  exact
    norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_apply_le_twoA
      hν U₀ hA hU₀
      (h3ClampUnitTime
        (s / h3FinHeatLerayRestartRadius ν A))

/-- On every physical time inside the canonical restart window, the spatial
Fréchet derivative of the selected-path nonlinear Duhamel reconstruction has
the generic `sqrt t` bound with both path norms replaced by `2A`. -/
theorem norm_fderiv_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 ≤ t)
    (_htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i)
        x‖
      ≤
    3 *
      ((2 * Real.pi) *
        (2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t *
          h3NonlinearForcingL1Coefficient * (2 * A) * (2 * A))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hW :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖W s‖ ≤ 2 * A := by
    intro s _hs
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  exact
    norm_fderiv_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_le
      hν ht h2A h2A
      W W
      hWcont hWcont
      hW hW
      i x

/-- Quantitative spatial Fréchet bound for the complete canonical restart
step. -/
theorem norm_fderiv_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_atRestartRadius_le
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let R : ℝ := h3FinHeatLerayRestartRadius ν A
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν R W W i)
        x‖
      ≤
    3 *
      ((2 * Real.pi) *
        (2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt R *
          h3NonlinearForcingL1Coefficient * (2 * A) * (2 * A))) := by
  dsimp only
  exact
    norm_fderiv_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_le
      hν U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      (le_refl (h3FinHeatLerayRestartRadius ν A))
      i x

end

end Euclidean
end Bridge
end PrimeTensor
