import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.SelectedC1Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.HeadLocalFubini
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.GlobalFubini
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Spatial.Derivative

/-!
# Pointwise identification of the full selected Duhamel reconstruction

The head and tail source-time/Fourier interchanges are now both complete.

For the midpoint head, two explicit Fourier representatives of the same named
deweighted `L²` state are available:

* the older positive-time heat representative used by
  `h3SelectedDuhamelRawFourierAmplitude`;
* the new source-time-integrated head raw amplitude used by the global Fubini
  theorem.

Their common `L²` state identifies those two functions almost everywhere.
Consequently the full selected raw amplitude can be replaced, without changing
its inverse Fourier transform, by

    headRawAmplitude + tailRawAmplitude.

Ordinary inverse Fourier reconstruction is additive for these two `L¹`
amplitudes.  The two already-proved global Fubini identities then identify the
summands with the classical retarded integrals on `0..t/2` and `t/2..t`.
Finally interval additivity joins them into the classical pointwise Duhamel
integral on `0..t`.

This is the pointwise nonlinear classicalization bridge.  No `L²` point
evaluation is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedFullPointwise
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The positive-time heat amplitude previously used for the selected midpoint
head and the explicit source-time-integrated head amplitude agree almost
everywhere. -/
theorem h3SelectedDuhamelHeadHeatRawRepresentative_ae_eq_headRawFourierAmplitude
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
    h3SpectralScalarHeatRawRepresentative
        ν (t / 2)
        (h3SpectralFinHeatLerayDuhamel
          ν (t / 2) hν W W i)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SelectedDuhamelHeadRawFourierAmplitude
      ν A t hν U₀ hA hU₀ i := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hHeat :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heatRepresentative
      hν U₀ hA hU₀ ht i

  have hRaw :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  dsimp only [W] at hHeat ⊢
  exact hHeat.symm.trans hRaw

/-- The full explicit selected raw amplitude may be represented almost
everywhere as the sum of the source-integrated midpoint head and terminal
tail amplitudes. -/
theorem h3SelectedDuhamelRawFourierAmplitude_ae_eq_headRaw_add_tailRaw
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    h3SelectedDuhamelRawFourierAmplitude
        ν A t hν U₀ hA hU₀ ht i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (h3SelectedDuhamelHeadRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i
      +
    h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hHead :=
    h3SelectedDuhamelHeadHeatRawRepresentative_ae_eq_headRawFourierAmplitude
      hν U₀ hA hU₀ ht i

  dsimp only [W] at hHead

  filter_upwards [hHead] with ξ hξ

  unfold h3SelectedDuhamelRawFourierAmplitude
  dsimp only [W, Pi.add_apply]
  rw [hξ]

/-- Inside the restart radius, the canonical pointwise selected Duhamel
reconstruction is exactly the classical retarded Duhamel integral, at every
spatial point. -/
theorem h3SelectedDuhamelC1Representative_eq_C3Duhamel
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
    h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i
      =
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
      ν t W W i := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let H : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelHeadRawFourierAmplitude
      ν A t hν U₀ hA hU₀ i

  let T : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailRawFourierAmplitude
      ν A t hν U₀ hA hU₀ i

  have hAmpEq :
      h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i
        =ᵐ[(volume : Measure H3FourierPoint3)]
      H + T := by
    dsimp only [H, T]
    exact
      h3SelectedDuhamelRawFourierAmplitude_ae_eq_headRaw_add_tailRaw
        hν U₀ hA hU₀ ht i

  have hH :
      Integrable H (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SelectedDuhamelHeadRawFourierAmplitude_integrable_global
        hν U₀ hA hU₀ ht i

  have hT :
      Integrable T (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact
      h3SelectedDuhamelTailRawFourierAmplitude_integrable_global
        hν U₀ hA hU₀ ht htR i

  have hInnerNegContinuous :
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          -inner ℝ p.1 p.2)
    exact
      (continuous_inner
        (𝕜 := ℝ)
        (E := H3FourierPoint3)).neg

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWbound :
      ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  funext x

  have hInvEq :
      h3SelectedDuhamelC1Representative
          ν A t hν U₀ hA hU₀ ht i x
        =
      FourierTransformInv.fourierInv (H + T) x := by
    unfold h3SelectedDuhamelC1Representative
    exact
      _root_.Real.fourierInv_congr_ae hAmpEq x

  have hInvAdd :
      FourierTransformInv.fourierInv (H + T) x
        =
      FourierTransformInv.fourierInv H x
        +
      FourierTransformInv.fourierInv T x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (H + T)
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          H
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          T
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          hH
          hT)
        x

  have hHead :
      FourierTransformInv.fourierInv H x
        =
      ∫ s in (0 : ℝ)..(t / 2),
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t W W i x s := by
    dsimp only [H, W]
    exact
      h3SelectedDuhamelHeadFourierInv_eq_C3IntervalIntegral
        hν U₀ hA hU₀ ht i x

  have hTail :
      FourierTransformInv.fourierInv T x
        =
      ∫ s in (t / 2)..t,
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t W W i x s := by
    dsimp only [T, W]
    exact
      h3SelectedDuhamelTailFourierInv_eq_C3IntervalIntegral
        hν U₀ hA hU₀ ht htR i x

  let R : ℝ → ℂ :=
    fun s =>
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t W W i x s

  have hR :
      IntervalIntegrable R volume (0 : ℝ) t := by
    dsimp only [R]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_intervalIntegrable_of_continuous
        hν
        ht.le
        h2A
        h2A
        W
        W
        hWcont
        hWcont
        (fun s _hs => hWbound s)
        (fun s _hs => hWbound s)
        i
        x

  have hhalf0 : 0 ≤ t / 2 := by
    linarith

  have hhalft : t / 2 ≤ t := by
    linarith

  have hRLong :
      IntegrableOn R (Set.Ioc (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hR

  have hRHead :
      IntervalIntegrable R volume (0 : ℝ) (t / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf0]
    exact
      hRLong.mono_set
        (by
          intro s hs
          exact ⟨hs.1, by linarith [hs.2]⟩)

  have hRTail :
      IntervalIntegrable R volume (t / 2) t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalft]
    exact
      hRLong.mono_set
        (by
          intro s hs
          exact ⟨by linarith [hs.1, ht], hs.2⟩)

  have hSplit :
      (∫ s in (0 : ℝ)..(t / 2), R s)
        +
      (∫ s in (t / 2)..t, R s)
        =
      ∫ s in (0 : ℝ)..t, R s :=
    intervalIntegral.integral_add_adjacent_intervals
      hRHead hRTail

  calc
    h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i x
        =
      FourierTransformInv.fourierInv (H + T) x :=
      hInvEq
    _ =
      FourierTransformInv.fourierInv H x
        +
      FourierTransformInv.fourierInv T x :=
      hInvAdd
    _ =
      (∫ s in (0 : ℝ)..(t / 2), R s)
        +
      (∫ s in (t / 2)..t, R s) := by
      dsimp only [R] at hHead hTail ⊢
      rw [hHead, hTail]
    _ =
      ∫ s in (0 : ℝ)..t, R s :=
      hSplit
    _ =
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i x := by
      rfl

end

end Euclidean
end Bridge
end PrimeTensor
