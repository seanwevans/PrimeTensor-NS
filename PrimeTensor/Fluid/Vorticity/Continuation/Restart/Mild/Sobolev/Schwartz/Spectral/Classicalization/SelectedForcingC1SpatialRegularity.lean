import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.C0.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.FirstForcingMass
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Classicalization: spatial C¹ regularity of the selected instantaneous forcing

The mixed spacetime frontier differentiates the selected temporal derivative
candidate once in space.  Its nonlinear endpoint term is the instantaneous
unheated Leray forcing

    N(W(t), W(t)).

The existing `C0` reconstruction only records continuity of this inverse
Fourier transform.  However, the selected forcing moment stack is already
strictly stronger: `SelectedForcingFirst` proves that the raw forcing retains
one integrable Fourier moment at every positive restart time.

Mathlib's Fourier differentiation theorem turns exactly that first moment into
`C¹` regularity of the ordinary Fourier transform.  Composing with negation
gives the inverse transform, and composing with the canonical `Point3`/`WithLp`
coordinate equivalence gives the physical carrier version.

Thus this file spends no new nonlinear estimate.  It exposes spatial
regularity that was already quantitatively present in the selected first
forcing moment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingC1SpatialRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected instantaneous complex forcing is spatially `C¹` on the
Fourier Euclidean carrier at every positive time up to the restart radius. -/
theorem h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_one
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
    ContDiff ℝ 1
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

  have hMoments :
      ∀ (n : ℕ),
        (n : ℕ∞) ≤ (1 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hnNat : n ≤ 1 := by
      exact_mod_cast hn
    interval_cases n
    · simpa only [pow_zero, one_mul] using hZero.norm
    · simpa only [pow_one] using hOne

  have hFourier :
      ContDiff ℝ 1
        (FourierTransform.fourier f) := by
    exact
      Real.contDiff_fourier hMoments

  have hNeg :
      ContDiff ℝ 1
        (fun x : H3FourierPoint3 => -x) := by
    fun_prop

  have hInv :
      ContDiff ℝ 1
        (fun x : H3FourierPoint3 =>
          FourierTransformInv.fourierInv f x) := by
    have hComp :
        ContDiff ℝ 1
          (fun x : H3FourierPoint3 =>
            FourierTransform.fourier f (-x)) :=
      hFourier.comp hNeg

    simpa only [Real.fourierInv_eq_fourier_neg] using hComp

  simpa only [
    f,
    W,
    h3RawFinLerayOuterProductDivergenceC0Representative
  ] using hInv

/-- Transporting the selected instantaneous forcing to the project's `Point3`
carrier preserves spatial `C¹` regularity. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_contDiff_one
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
    ContDiff ℝ 1
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hForcing :
      ContDiff ℝ 1
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_one
        hν U₀ hA hU₀ ht htR i

  have hToLp :
      ContDiff ℝ 1
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) := by
    exact
      (PiLp.contDiff_toLp :
        ContDiff ℝ 1
          (WithLp.toLp 2 : Point3 → H3FourierPoint3))

  unfold
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3

  exact
    hForcing.comp hToLp

/-- The real part of the selected instantaneous forcing is spatially `C¹` on
the physical `Point3` carrier.  This is the form needed by the selected real
temporal derivative candidate. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_one
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
    ContDiff ℝ 1
      (fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i x).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hForcing :
      ContDiff ℝ 1
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_contDiff_one
        hν U₀ hA hU₀ ht htR i

  change ContDiff ℝ 1
    (Complex.reCLM ∘
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i)
  exact Complex.reCLM.contDiff.comp hForcing

end

end Euclidean
end Bridge
end PrimeTensor
