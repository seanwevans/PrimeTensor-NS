import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralFinHeatLerayVariationOfConstantsState
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Restart.Radius

/-!
# Classicalization: selected restart variation-of-constants reduction

The general Fourier-mode route has now been reconstructed all the way back to
the actual weighted spectral H³ state:

    W(t) = H_t W(0) - D[W,W](t).

This file returns that theorem to the canonical Banach-selected restart path.

The legacy restart-radius physical-extension module predates the current
`Sobolev.Fourier.Derivative` hierarchy.  Rather than mixing that stale import
branch with the modern classicalization stack, we define the canonical physical
extension directly from the current restart-radius path and the current
`h3PathPhysicalRealExtension`.

For this selected path, global Banach continuity and the uniform `2A` bound are
not new hypotheses: both follow directly from the clamped physical-time
extension of the fixed point.  Consequently the general state-level
variation-of-constants theorem reduces to exactly the three fixed-frequency
inputs isolated earlier:

* continuity in source time of each raw Fourier mode;
* the concrete heat--Leray Fourier-mode ODE on the strict time interval;
* weighted source-time integrability of the concrete Leray forcing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVariationOfConstantsStateReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical globally indexed physical-time extension of the modern
restart-radius Banach solution.  This is defined directly from the current
`Fin.Heat.Leray.Restart.Radius` hierarchy, avoiding the legacy flat Sobolev
import branch. -/
noncomputable def h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    ℝ → H3SpectralVelocityState :=
  h3PathPhysicalRealExtension
    (h3FinHeatLerayRestartRadius ν A)
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadius
      hν U₀ hA hU₀)

/-- For the canonical selected restart path, the state-level
variation-of-constants identity follows from the three remaining
fixed-frequency mode hypotheses.  Continuity and the global `2A` Banach bound
are discharged from the fixed-point construction itself. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_variationOfConstants_state_of_mode_data
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (_htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hFContinuous :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier
              ((h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
                hν U₀ hA hU₀) s i) ξ)
          (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ ξ : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) t,
          H3FinHeatLerayModeODEAt
            ν ξ
            (h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
              hν U₀ hA hU₀)
            s)
    (hWeightedForcing :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        IntervalIntegrable
          (fun s : ℝ =>
            Real.exp
                (ν * h3FourierGradientSquare ξ * s)
              •
            h3RawFinLerayOuterProductDivergence
              ((h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
                hν U₀ hA hU₀) s)
              ((h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
                hν U₀ hA hU₀) s)
              i ξ)
          volume
          0
          t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    W t
      =
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk t ht.le) (W 0)
      -
    h3SpectralFinHeatLerayDuhamel
      ν t hν W W := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWcont : Continuous W := by
    dsimp only [
      W,
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
    ]
    exact
      continuous_h3PathPhysicalRealExtension
        (h3FinHeatLerayRestartRadius ν A)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadius
          hν U₀ hA hU₀)

  have hWbound :
      ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    change
      ‖h3SpectralFinHeatLerayMildSolutionAtRestartRadius
          hν U₀ hA hU₀
          (h3ClampUnitTime
            (s / h3FinHeatLerayRestartRadius ν A))‖
        ≤
      2 * A
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_apply_le_twoA
        hν U₀ hA hU₀
        (h3ClampUnitTime
          (s / h3FinHeatLerayRestartRadius ν A))

  have hM : 0 ≤ 2 * A := by
    positivity

  have hFContinuous' :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier (W s i) ξ)
          (Set.Icc (0 : ℝ) t) := by
    simpa only [W] using hFContinuous

  have hODE' :
      ∀ ξ : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) t,
          H3FinHeatLerayModeODEAt ν ξ W s := by
    simpa only [W] using hODE

  have hWeightedForcing' :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        IntervalIntegrable
          (fun s : ℝ =>
            Real.exp
                (ν * h3FourierGradientSquare ξ * s)
              •
            h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ)
          volume
          0
          t := by
    simpa only [W] using hWeightedForcing

  have hState :=
    h3FinHeatLerayVariationOfConstants_retarded_state
      hν ht hM W hWcont hWbound
      hFContinuous' hODE' hWeightedForcing'

  simpa only [W] using hState

end

end Euclidean
end Bridge
end PrimeTensor
