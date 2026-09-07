import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Force
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.Selected.Convolution.Second
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Spatial C² regularity of the selected positive-time pressure

A generic H³ pressure only inherits one raw Fourier moment from the unheated
H³ product algebra, so `Pressure.C1` correctly stops at classical `C¹`.

The canonical selected mild restart is stronger at every strict positive time.
`SelectedConvolutionSecond` proves that every raw product convolution

    rawConv(W(t)_k, W(t)_j)

has an integrable second Fourier moment.  The pressure multiplier is an
order-zero finite sum

    p̂
      =
    - Σₖ Σⱼ Rⱼₖ rawConv(Wₖ,Wⱼ),

and every rank-one Leray coefficient satisfies `‖Rⱼₖ‖ ≤ 1`.

Therefore the selected pressure itself has an integrable second Fourier moment.
Mathlib's Fourier differentiability theorem then upgrades the canonical
inverse-Fourier pressure representative directly to spatial `C²`.

No new nonlinear estimate is introduced here: this file only transports the
already-closed selected second convolution moment through the bounded pressure
multiplier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal FourierTransform Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedPressureC2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strict positive selected restart time, the pressure Fourier
amplitude has an integrable second raw moment. -/
theorem h3RawFinPressureFourier_selectedRestart_secondMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3RawFinPressureFourier (W t) (W t) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hMajorantExpanded :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ k : Fin 3,
            ∑ j : Fin 3,
              ‖ξ‖ ^ 2 *
                ‖h3RawProductConvolution
                  (W t k) (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      integrable_finset_sum
        (Finset.univ : Finset (Fin 3))
        (fun k _ =>
          integrable_finset_sum
            (Finset.univ : Finset (Fin 3))
            (fun j _ =>
              h3RawProductConvolution_selectedRestart_secondMoment_integrable
                hν U₀ hA hU₀ ht htR k j))

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            (∑ k : Fin 3,
              ∑ j : Fin 3,
                ‖h3RawProductConvolution
                  (W t k) (W t j) ξ‖))
        (volume : Measure H3FourierPoint3) := by
    simpa only [Finset.mul_sum] using hMajorantExpanded

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawFinPressureFourier (W t) (W t) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      (continuous_norm.pow 2).aestronglyMeasurable.mul
        (h3RawFinPressureFourier_integrable
          (W t) (W t)).norm.aestronglyMeasurable

  refine Integrable.mono' hMajorant hTargetMeas ?_
  filter_upwards with ξ

  rw [
    h3RawFinPressureFourier_eq_neg_sum_rankOne_rawProductConvolution
  ]
  rw [norm_neg]

  have hNorm :
      ‖∑ k : Fin 3,
          ∑ j : Fin 3,
            h3LerayRankOneCoefficient ξ j k *
              h3RawProductConvolution
                (W t k) (W t j) ξ‖
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          ‖h3RawProductConvolution
            (W t k) (W t j) ξ‖ := by
    calc
      ‖∑ k : Fin 3,
          ∑ j : Fin 3,
            h3LerayRankOneCoefficient ξ j k *
              h3RawProductConvolution
                (W t k) (W t j) ξ‖
          ≤
        ∑ k : Fin 3,
          ‖∑ j : Fin 3,
            h3LerayRankOneCoefficient ξ j k *
              h3RawProductConvolution
                (W t k) (W t j) ξ‖ := by
            exact norm_sum_le _ _
      _ ≤
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            ‖h3LerayRankOneCoefficient ξ j k *
              h3RawProductConvolution
                (W t k) (W t j) ξ‖ := by
            exact
              Finset.sum_le_sum
                (fun k _ => norm_sum_le _ _)
      _ ≤
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            ‖h3RawProductConvolution
              (W t k) (W t j) ξ‖ := by
            exact
              Finset.sum_le_sum
                (fun k _ =>
                  Finset.sum_le_sum
                    (fun j _ => by
                      rw [norm_mul]
                      exact
                        mul_le_of_le_one_left
                          (norm_nonneg
                            (h3RawProductConvolution
                              (W t k) (W t j) ξ))
                          (norm_h3LerayRankOneCoefficient_le_one
                            ξ j k)))

  have hMul :
      ‖ξ‖ ^ 2 *
          ‖∑ k : Fin 3,
              ∑ j : Fin 3,
                h3LerayRankOneCoefficient ξ j k *
                  h3RawProductConvolution
                    (W t k) (W t j) ξ‖
        ≤
      ‖ξ‖ ^ 2 *
        (∑ k : Fin 3,
          ∑ j : Fin 3,
            ‖h3RawProductConvolution
              (W t k) (W t j) ξ‖) :=
    mul_le_mul_of_nonneg_left
      hNorm
      (pow_nonneg (norm_nonneg ξ) 2)

  have hLeftNonneg :
      0 ≤
        ‖ξ‖ ^ 2 *
          ‖∑ k : Fin 3,
              ∑ j : Fin 3,
                h3LerayRankOneCoefficient ξ j k *
                  h3RawProductConvolution
                    (W t k) (W t j) ξ‖ := by
    positivity

  simpa [
    Real.norm_eq_abs,
    abs_of_nonneg hLeftNonneg
  ] using hMul

/-- Selected pressure Fourier moments through order two are integrable. -/
theorem h3RawFinPressureFourier_selectedRestart_moment_integrable_two
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (n : ℕ)
    (hn : n ≤ 2) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ n *
          ‖h3RawFinPressureFourier (W t) (W t) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hnCases : n = 0 ∨ n = 1 ∨ n = 2 := by
    omega

  rcases hnCases with rfl | rfl | rfl
  · simpa using
      (h3RawFinPressureFourier_integrable
        (W t) (W t)).norm
  · simpa using
      h3RawFinPressureFourier_firstMoment_integrable
        (W t) (W t)
  · simpa only [W] using
      h3RawFinPressureFourier_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR

/-- The canonical complex selected pressure reconstruction is spatially `C²`
at every strict positive restart time. -/
theorem h3RawFinPressureC1Representative_selectedRestart_contDiff_two
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContDiff ℝ 2
      (h3RawFinPressureC1Representative
        (W t) (W t)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hFourier :
      ContDiff ℝ 2
        (FourierTransform.fourier
          (h3RawFinPressureFourier
            (W t) (W t))) := by
    apply Real.contDiff_fourier
    intro n hn
    have hn' : n ≤ 2 := by
      simpa using hn
    exact
      h3RawFinPressureFourier_selectedRestart_moment_integrable_two
        hν U₀ hA hU₀ ht htR n hn'

  have hEq :
      h3RawFinPressureC1Representative
          (W t) (W t)
        =
      fun x : H3FourierPoint3 =>
        FourierTransform.fourier
          (h3RawFinPressureFourier
            (W t) (W t))
          (-x) := by
    funext x
    unfold h3RawFinPressureC1Representative
    exact
      Real.fourierInv_eq_fourier_neg
        (h3RawFinPressureFourier
          (W t) (W t))
        x

  rw [hEq]
  exact hFourier.comp (by fun_prop)

/-- Taking real parts preserves the selected pressure `C²` regularity. -/
theorem h3RawFinPressureRealC1Representative_selectedRestart_contDiff_two
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContDiff ℝ 2
      (h3RawFinPressureRealC1Representative
        (W t) (W t)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  unfold h3RawFinPressureRealC1Representative

  simpa [Function.comp_def] using
    (h3RawFinPressureC1Representative_selectedRestart_contDiff_two
      hν U₀ hA hU₀ ht htR).continuousLinearMap_comp
        Complex.reCLM

/-- Transport to `Point3` preserves selected pressure `C²` regularity. -/
theorem h3RawFinPressureRealC1RepresentativeOnPoint3_selectedRestart_contDiff_two
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContDiff ℝ 2
      (h3RawFinPressureRealC1RepresentativeOnPoint3
        (W t) (W t)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hPressure :
      ContDiff ℝ 2
        (h3RawFinPressureRealC1Representative
          (W t) (W t)) := by
    dsimp only [W]
    exact
      h3RawFinPressureRealC1Representative_selectedRestart_contDiff_two
        hν U₀ hA hU₀ ht htR

  have hToLp :
      ContDiff ℝ 2
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) := by
    exact PiLp.contDiff_toLp

  unfold h3RawFinPressureRealC1RepresentativeOnPoint3

  exact hPressure.comp hToLp

/-- Spacetime-path packaging: the canonical pressure generated by the selected
restart is spatially `C²` at every strict positive restart time. -/
theorem h3RawFinPressureRealC1OfPath_selectedRestart_spatialC2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    SpatialC2
      (h3RawFinPressureRealC1OfPath W t) := by
  dsimp only

  unfold
    SpatialC2
    h3RawFinPressureRealC1OfPath

  exact
    h3RawFinPressureRealC1RepresentativeOnPoint3_selectedRestart_contDiff_two
      hν U₀ hA hU₀ ht htR

end

end Euclidean
end Bridge
end PrimeTensor
