import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Head.Real.C3.Selected
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedProfileFullIntegral

/-!
# Selected terminal Duhamel tail: second Fourier-moment budget

The selected midpoint decomposition isolates the only part of the Duhamel term
whose heat lag can vanish:

    Tail(t) = ∫_{t/2}^t H_{t-s} N(W(s),W(s)) ds.

The endpoint-quarter branch has already proved genuine source-time
integrability of the corresponding second Fourier-moment profile.  This file
packages that fact directly for the named selected tail and records the
terminal-half budget in the exact time-outer / frequency-inner form needed by
the forthcoming Fubini/bootstrap step.

No interchange of the source-time and frequency integrals is made here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedDuhamelTailSecondMoment
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The scalar second Fourier-moment mass carried by the selected terminal
Duhamel half-tail in one velocity coordinate. -/
noncomputable def h3SpectralFinHeatLerayDuhamelSelectedTailSecondMomentMass
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) : ℝ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  ∫ s in (t / 2)..t,
    h3NonlinearForcingHeatSecondMomentProfile ν t W i s

/-- The selected terminal second-moment profile is genuinely interval
integrable. -/
theorem h3NonlinearForcingHeatSecondMomentProfile_selectedDuhamelTail_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntervalIntegrable
      (h3NonlinearForcingHeatSecondMomentProfile ν t W i)
      volume
      (t / 2)
      t := by
  dsimp only
  exact
    h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_halfTail_intervalIntegrable
      hν U₀ hA hU₀ ht htR i

/-- The selected terminal second-moment mass is nonnegative. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailSecondMomentMass_nonneg
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    0 ≤
      h3SpectralFinHeatLerayDuhamelSelectedTailSecondMomentMass
        ν A t hν U₀ hA hU₀ i := by
  unfold h3SpectralFinHeatLerayDuhamelSelectedTailSecondMomentMass

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  change
    0 ≤
      ∫ s in (t / 2)..t,
        h3NonlinearForcingHeatSecondMomentProfile ν t W i s

  have hhalf : t / 2 ≤ t := by
    linarith

  exact
    intervalIntegral.integral_nonneg hhalf
      (fun s _hs =>
        h3NonlinearForcingHeatSecondMomentProfile_nonneg
          ν t W i s)

/-- The terminal-half second-moment mass is controlled by the canonical
selected restart second-moment budget. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailSecondMomentMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralFinHeatLerayDuhamelSelectedTailSecondMomentMass
        ν A t hν U₀ hA hU₀ i
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let P : ℝ → ℝ :=
    h3NonlinearForcingHeatSecondMomentProfile ν t W i

  have hBudget :
      ‖∫ s in (0 : ℝ)..(t / 2), P s‖
        +
      ‖∫ s in (t / 2)..t, P s‖
        ≤
      h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
    dsimp only [P, W]
    exact
      norm_h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_head_add_halfTail_le
        hν U₀ hA hU₀ ht htR i

  have hTail0 :
      0 ≤ ∫ s in (t / 2)..t, P s := by
    have hhalf : t / 2 ≤ t := by
      linarith
    exact
      intervalIntegral.integral_nonneg hhalf
        (fun s _hs => by
          dsimp only [P]
          exact
            h3NonlinearForcingHeatSecondMomentProfile_nonneg
              ν t W i s)

  change
    (∫ s in (t / 2)..t, P s)
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t

  calc
    (∫ s in (t / 2)..t, P s)
        =
      ‖∫ s in (t / 2)..t, P s‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hTail0]
    _ ≤
      ‖∫ s in (0 : ℝ)..(t / 2), P s‖
        +
      ‖∫ s in (t / 2)..t, P s‖ := by
        exact
          le_add_of_nonneg_left
            (norm_nonneg
              (∫ s in (0 : ℝ)..(t / 2), P s))
    _ ≤
      h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t :=
        hBudget

/-- Direct time-outer / frequency-inner form of the selected terminal-tail
second Fourier-moment budget. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_selectedDuhamelTail_secondMoment_timeFrequencyIntegral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ s in (t / 2)..t,
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
  dsimp only

  have hMass :=
    h3SpectralFinHeatLerayDuhamelSelectedTailSecondMomentMass_le
      hν U₀ hA hU₀ ht htR i

  simpa only [
    h3SpectralFinHeatLerayDuhamelSelectedTailSecondMomentMass,
    h3NonlinearForcingHeatSecondMomentProfile
  ] using hMass

end
end Euclidean
end Bridge
end PrimeTensor
