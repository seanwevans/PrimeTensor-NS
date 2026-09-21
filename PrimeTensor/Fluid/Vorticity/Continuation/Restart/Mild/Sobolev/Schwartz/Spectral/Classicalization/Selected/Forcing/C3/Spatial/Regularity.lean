import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C2.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Third.Forcing.Mass

/-!
# Classicalization: spatial C³ regularity of the selected instantaneous forcing

The selected nonlinear forcing now has an integrable cubic raw Fourier moment
at every positive restart time.  Applying the same Fourier differentiability
argument used for the existing `C¹` and `C²` layers exposes genuine spatial
`C³` regularity.

This file packages three equivalent forms:

* the complex Fourier-carrier representative is `ContDiff ℝ 3`;
* its `Point3` pullback is `ContDiff ℝ 3`;
* the real physical forcing coordinate is `ContDiff ℝ 3`.

No new nonlinear estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingC3SpatialRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every selected instantaneous forcing coordinate is spatially `C³` on the
Fourier carrier at strict positive restart times. -/
theorem h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_three
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
    ContDiff ℝ 3
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

  have hThree :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMoments :
      ∀ (n : ℕ),
        (n : ℕ∞) ≤ (3 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hnNat : n ≤ 3 := by
      exact_mod_cast hn
    interval_cases n
    · simpa only [pow_zero, one_mul] using hZero.norm
    · simpa only [pow_one] using hOne
    · simpa only using hTwo
    · simpa only using hThree

  have hFourier :
      ContDiff ℝ 3
        (FourierTransform.fourier f) := by
    exact
      Real.contDiff_fourier hMoments

  have hNeg :
      ContDiff ℝ 3
        (fun x : H3FourierPoint3 => -x) := by
    fun_prop

  have hInv :
      ContDiff ℝ 3
        (fun x : H3FourierPoint3 =>
          FourierTransformInv.fourierInv f x) := by
    have hComp :
        ContDiff ℝ 3
          (fun x : H3FourierPoint3 =>
            FourierTransform.fourier f (-x)) :=
      hFourier.comp hNeg

    simpa only [Real.fourierInv_eq_fourier_neg] using hComp

  simpa only [
    f,
    W,
    h3RawFinLerayOuterProductDivergenceC0Representative
  ] using hInv

/-- Pulling the selected complex forcing representative back to `Point3`
preserves spatial `C³` regularity. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_contDiff_three
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
    ContDiff ℝ 3
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hForcing :
      ContDiff ℝ 3
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_three
        hν U₀ hA hU₀ ht htR i

  have hToLp :
      ContDiff ℝ 3
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) := by
    exact PiLp.contDiff_toLp

  unfold
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3

  exact hForcing.comp hToLp

/-- Taking the real part gives the concrete selected physical forcing
coordinate with spatial `C³` regularity. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_three
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
    ContDiff ℝ 3
      (fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i x).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hForcing :
      ContDiff ℝ 3
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_contDiff_three
        hν U₀ hA hU₀ ht htR i

  change ContDiff ℝ 3
    (Complex.reCLM ∘
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i)

  exact Complex.reCLM.contDiff.comp hForcing

end

end Euclidean
end Bridge
end PrimeTensor
