import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.ProfileContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedFrozenTimeIntegrable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedAEMajorant
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedTailFrequencyTriangle

/-!
# Genuine time integrability of the selected second-moment profile

The named selected profile is now continuous at every strict retarded time.
This closes the measurability obligation that earlier scalar domination
estimates intentionally did not supply.

On the old half-head `0..t/2`, continuity on a compact interval gives
integrability directly.  On the terminal half, the actual unsplit profile is
dominated almost everywhere by the sum of:

* the quarter-cancelled endpoint majorant; and
* the already-integrable frozen terminal profile.

The endpoint `s=t` is removed by the standard `Ioc/Ioo` equivalence.  The two
halves then combine to prove genuine `IntervalIntegrable` on `0..t`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedProfileTimeIntegrable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected second-moment profile is genuinely interval-integrable on the
old half-head. -/
theorem h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_halfHead_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntervalIntegrable
      (h3NonlinearForcingHeatSecondMomentProfile ν t W i)
      volume
      0
      (t / 2) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hhalfLt : t / 2 < t := by
    linarith

  have hContIio :
      ContinuousOn
        (h3NonlinearForcingHeatSecondMomentProfile ν t W i)
        (Set.Iio t) := by
    dsimp only [W]
    exact
      continuousOn_h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_Iio
        hν U₀ hA hU₀ i

  have hCont :
      ContinuousOn
        (h3NonlinearForcingHeatSecondMomentProfile ν t W i)
        (Set.Icc (0 : ℝ) (t / 2)) := by
    exact
      hContIio.mono
        (by
          intro s hs
          exact lt_of_le_of_lt hs.2 hhalfLt)

  have htHalf0 : (0 : ℝ) ≤ t / 2 := by
    linarith

  have hContUIcc :
      ContinuousOn
        (h3NonlinearForcingHeatSecondMomentProfile ν t W i)
        (Set.uIcc (0 : ℝ) (t / 2)) := by
    rw [Set.uIcc_of_le htHalf0]
    exact hCont

  exact hContUIcc.intervalIntegrable

/-- The selected unsplit terminal half-tail profile is genuinely
interval-integrable. -/
theorem h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_halfTail_intervalIntegrable
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

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let P : ℝ → ℝ :=
    h3NonlinearForcingHeatSecondMomentProfile ν t W i

  let D : ℝ → ℝ := fun s =>
    ∫ ξ : H3FourierPoint3,
      ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν (t - s) ξ *
          (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
            h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖

  let G : ℝ → ℝ := fun s =>
    ∫ ξ : H3FourierPoint3,
      ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν (t - s) ξ *
          h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖

  let Q : ℝ → ℝ :=
    h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
      ν t
      (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
        ν A (t / 2) t)

  have hhalfPos : 0 < t / 2 := by
    exact div_pos ht (by norm_num)

  have hhalf : t / 2 ≤ t := by
    linarith

  have hhalfLt : t / 2 < t := by
    linarith

  have hQOpen :
      Integrable Q
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) := by
    dsimp only [Q]
    exact
      h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant_integrableOn_Ioo_selectedRestart
        (ν := ν) (A := A) hhalf

  have hGInt :
      IntervalIntegrable G volume (t / 2) t := by
    dsimp only [G, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeFrequencyProfile_intervalIntegrable
        hν U₀ hA hU₀ ht i

  have hGOpen :
      Integrable G
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf] at hGInt
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hGInt
    exact hGInt

  have hMajorant :
      Integrable (fun s : ℝ => Q s + G s)
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) :=
    hQOpen.add hGOpen

  have hContIio :
      ContinuousOn P (Set.Iio t) := by
    dsimp only [P, W]
    exact
      continuousOn_h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_Iio
        hν U₀ hA hU₀ i

  have hContOpen :
      ContinuousOn P (Set.Ioo (t / 2) t) := by
    exact
      hContIio.mono
        (by
          intro s hs
          exact hs.2)

  have hPMeas :
      AEStronglyMeasurable P
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) :=
    hContOpen.aestronglyMeasurable measurableSet_Ioo

  have hCancelAE :
      ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)),
        D s ≤ Q s := by
    simpa only [D, Q, W] using
      (h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_le_quarter_selectedRestart_ae
        hν U₀ hA hU₀ hhalfPos hhalfLt htR i)

  have hBoundAE :
      ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)),
        ‖P s‖ ≤ Q s + G s := by
    rw [ae_restrict_iff' measurableSet_Ioo] at hCancelAE ⊢
    filter_upwards [hCancelAE] with s hCancel
    intro hs

    have hTri0 :=
      h3RawFinLerayOuterProductDivergenceHeat_secondMoment_frequencyIntegral_le_endpointDifference_add_frozen
        hν hs.2 W i

    have hTri : P s ≤ D s + G s := by
      simpa only [P, D, G, W,
        h3NonlinearForcingHeatSecondMomentProfile] using hTri0

    have hP0 : 0 ≤ P s := by
      dsimp only [P]
      exact
        h3NonlinearForcingHeatSecondMomentProfile_nonneg
          ν t W i s

    rw [Real.norm_eq_abs, abs_of_nonneg hP0]
    exact
      hTri.trans
        (add_le_add_left (hCancel hs) (G s))

  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf]
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]

  exact
    hMajorant.mono'
      hPMeas
      hBoundAE

/-- The selected second-moment profile is genuinely interval-integrable on the
full Duhamel source-time interval. -/
theorem h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_intervalIntegrable
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
      0
      t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hHead :
      IntervalIntegrable
        (h3NonlinearForcingHeatSecondMomentProfile ν t W i)
        volume 0 (t / 2) := by
    dsimp only [W]
    exact
      h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_halfHead_intervalIntegrable
        hν U₀ hA hU₀ ht i

  have hTail :
      IntervalIntegrable
        (h3NonlinearForcingHeatSecondMomentProfile ν t W i)
        volume (t / 2) t := by
    dsimp only [W]
    exact
      h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_halfTail_intervalIntegrable
        hν U₀ hA hU₀ ht htR i

  exact hHead.trans hTail

end

end Euclidean
end Bridge
end PrimeTensor
