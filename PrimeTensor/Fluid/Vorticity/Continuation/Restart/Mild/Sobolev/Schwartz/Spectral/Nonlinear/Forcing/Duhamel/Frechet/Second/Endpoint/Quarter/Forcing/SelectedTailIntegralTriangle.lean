import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedTailFrequencyTriangle
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedFrozenTimeIntegrable

/-!
# Selected quarter-Hölder forcing: integrated unsplit half-tail triangle

The terminal second-Duhamel kernel is naturally unsplit:

    H_{t-s} N(s).

The endpoint argument instead controls

    H_{t-s} (N(s) - N(t))

and the frozen terminal piece

    H_{t-s} N(t).

`Forcing.SelectedTailFrequencyTriangle` already proves the frequency-integrated
triangle inequality at every strict retarded source time.  The selected
quarter-cancellation majorant and the newly explicit frozen time integrability
put the two right-hand pieces on one genuinely interval-integrable majorant.

This file pushes the frequency triangle through the terminal half-time
integral and obtains an explicit bound for the unsplit terminal profile.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedTailIntegralTriangle
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit budget for the unsplit terminal half-tail after recombining the
endpoint-cancelled and frozen terminal forcing pieces. -/
noncomputable def h3NonlinearForcingQuarterSelectedRestartUnsplitHalfTailSecondMomentBudget
    (ν A t : ℝ) : ℝ :=
  12 * ν⁻¹ *
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
        ν A (t / 2) t *
      (t - t / 2) ^ ((1 : ℝ) / 4) +
    (((2 * Real.pi) ^ 2 * ν)⁻¹) *
      (4 * h3NonlinearForcingL1Coefficient * A ^ 2)

/-- The frequency-integrated unsplit terminal second-moment profile is bounded,
after time integration on `t/2..t`, by the sum of the selected cancelled-tail
budget and the selected frozen-terminal budget. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeat_secondMoment_unsplit_halfTail_intervalIntegral_le_quarter_selectedRestart
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
    ‖∫ s in (t / 2)..t,
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)‖
      ≤
    h3NonlinearForcingQuarterSelectedRestartUnsplitHalfTailSecondMomentBudget
      ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : ℝ → ℝ := fun s =>
    ∫ ξ : H3FourierPoint3,
      ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν (t - s) ξ *
          h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖

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

  have hQInt :
      IntervalIntegrable Q volume (t / 2) t := by
    dsimp only [Q]
    exact
      h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant_intervalIntegrable_selectedRestart

  have hGInt :
      IntervalIntegrable G volume (t / 2) t := by
    dsimp only [G, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeFrequencyProfile_intervalIntegrable
        hν U₀ hA hU₀ ht i

  have hMajorantInt :
      IntervalIntegrable (fun s : ℝ => Q s + G s) volume (t / 2) t :=
    hQInt.add hGInt

  have hCancelAE :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (t / 2) t)),
        D s ≤ Q s := by
    simpa only [D, Q, W] using
      (h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_le_quarter_selectedRestart_ae
        hν U₀ hA hU₀ hhalfPos hhalfLt htR i)

  have hCancelAmbient :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.Ioo (t / 2) t → D s ≤ Q s := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    exact hCancelAE

  have hOnIoo :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (t / 2) t)),
        ‖F s‖ ≤ Q s + G s := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hCancelAmbient] with s hsCancel
    intro hs

    have hTri0 :=
      h3RawFinLerayOuterProductDivergenceHeat_secondMoment_frequencyIntegral_le_endpointDifference_add_frozen
        hν hs.2 W i

    have hTri : F s ≤ D s + G s := by
      simpa only [F, D, G] using hTri0

    have hF0 : 0 ≤ F s := by
      dsimp only [F]
      exact integral_nonneg (fun ξ => by positivity)

    rw [Real.norm_eq_abs, abs_of_nonneg hF0]

    exact
      hTri.trans
        (add_le_add_left (hsCancel hs) (G s))

  have hOnIoc :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioc (t / 2) t)),
        ‖F s‖ ≤ Q s + G s := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact hOnIoo

  have hPointwise :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.Ioc (t / 2) t →
          ‖F s‖ ≤ Q s + G s := by
    rw [← ae_restrict_iff' measurableSet_Ioc]
    exact hOnIoc

  have hBound :
      ‖∫ s in (t / 2)..t, F s‖
        ≤
      ∫ s in (t / 2)..t, Q s + G s := by
    exact
      intervalIntegral.norm_integral_le_of_norm_le
        hhalf
        hPointwise
        hMajorantInt

  have hQExact :
      (∫ s in (t / 2)..t, Q s)
        =
      12 * ν⁻¹ *
          h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (t / 2) t *
          (t - t / 2) ^ ((1 : ℝ) / 4) := by
    simpa only [Q] using
      (h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant_integral_selectedRestart
        (ν := ν) (A := A) (a := t / 2) (t := t) hhalf)

  have hGBound :
      (∫ s in (t / 2)..t, G s)
        ≤
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
    simpa only [G, W] using
      (h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_time_frequencyIntegral_le_selectedRestart
        hν U₀ hA hU₀ ht i)

  change
    ‖∫ s in (t / 2)..t, F s‖
      ≤
    h3NonlinearForcingQuarterSelectedRestartUnsplitHalfTailSecondMomentBudget
      ν A t

  calc
    ‖∫ s in (t / 2)..t, F s‖
        ≤
      ∫ s in (t / 2)..t, Q s + G s := hBound
    _ =
      (∫ s in (t / 2)..t, Q s) +
        ∫ s in (t / 2)..t, G s := by
      exact intervalIntegral.integral_add hQInt hGInt
    _ ≤
      12 * ν⁻¹ *
          h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (t / 2) t *
          (t - t / 2) ^ ((1 : ℝ) / 4) +
        (((2 * Real.pi) ^ 2 * ν)⁻¹) *
          (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
      rw [hQExact]
      exact
        add_le_add_right
          hGBound
          (12 * ν⁻¹ *
            h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
              ν A (t / 2) t *
            (t - t / 2) ^ ((1 : ℝ) / 4))
    _ =
      h3NonlinearForcingQuarterSelectedRestartUnsplitHalfTailSecondMomentBudget
        ν A t := by
      rfl

end

end Euclidean
end Bridge
end PrimeTensor
