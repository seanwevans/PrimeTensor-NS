import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C1.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Second.Forcing.Mass

/-!
# Classicalization: spatial C² regularity of the selected instantaneous forcing

The selected nonlinear forcing already has an integrable second raw Fourier
moment at every positive restart time.  Applying the same Fourier
differentiability argument used for the existing `C¹` theorem exposes `C²`
regularity with no new nonlinear estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingC2SpatialRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

theorem h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_two
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
    ContDiff ℝ 2
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  have hZero :
      Integrable
        f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hOne :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hTwo :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMoments :
      ∀ (n : ℕ),
        (n : ℕ∞) ≤ (2 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hnNat : n ≤ 2 := by
      exact_mod_cast hn
    interval_cases n
    · simpa only [pow_zero, one_mul] using hZero.norm
    · simpa only [pow_one] using hOne
    · simpa only using hTwo

  have hFourier :
      ContDiff ℝ 2
        (FourierTransform.fourier f) := by
    exact
      Real.contDiff_fourier hMoments

  have hNeg :
      ContDiff ℝ 2
        (fun x : H3FourierPoint3 => -x) := by
    fun_prop

  have hInv :
      ContDiff ℝ 2
        (fun x : H3FourierPoint3 =>
          FourierTransformInv.fourierInv f x) := by
    have hComp :
        ContDiff ℝ 2
          (fun x : H3FourierPoint3 =>
            FourierTransform.fourier f (-x)) :=
      hFourier.comp hNeg

    simpa only [Real.fourierInv_eq_fourier_neg] using hComp

  simpa only [
    f,
    W,
    h3RawFinLerayOuterProductDivergenceC0Representative
  ] using hInv

theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_contDiff_two
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
    ContDiff ℝ 2
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hForcing :
      ContDiff ℝ 2
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_two
        hν U₀ hA hU₀ ht htR i

  have hToLp :
      ContDiff ℝ 2
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) := by
    exact PiLp.contDiff_toLp

  unfold
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3

  exact hForcing.comp hToLp

theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_two
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
    ContDiff ℝ 2
      (fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i x).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hForcing :
      ContDiff ℝ 2
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_contDiff_two
        hν U₀ hA hU₀ ht htR i

  change ContDiff ℝ 2
    (Complex.reCLM ∘
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i)

  exact Complex.reCLM.contDiff.comp hForcing

end

end Euclidean
end Bridge
end PrimeTensor
