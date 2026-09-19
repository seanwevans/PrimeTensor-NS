import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Selected.C2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Fourth.Convolution.Mass
import PrimeTensor.Bridge.Euclidean.Partials.Third
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Spatial C⁴ regularity of the selected positive-time pressure

The selected pressure was previously exported only at `C²`, because that file
used the selected second convolution moment.

The higher selected-mild development now already proves that every scalar raw
product convolution has an integrable fourth Fourier moment:

    ‖ξ‖⁴ |rawConv(W_k,W_j)| ∈ L¹.

The pressure multiplier is order zero and bounded coordinatewise by one, so the
same fourth moment passes directly to the pressure Fourier amplitude.  Together
with the unweighted `L¹` pressure amplitude this controls every natural moment
through order four, and Mathlib's Fourier differentiability theorem yields a
spatial `C⁴` pressure representative.

The final theorem packages the exact shape needed later by
`PressureSpatialC4OnTail`: every first intrinsic coordinate partial of the
selected pressure is spatially `C³`.

No new nonlinear or parabolic estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal FourierTransform Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedPressureC4
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Fourth pressure moment -/

/-- At every strict positive selected restart time, the pressure Fourier
amplitude has an integrable fourth raw moment. -/
theorem h3RawFinPressureFourier_selectedRestart_fourthMoment_integrable
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
        ‖ξ‖ ^ 4 *
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
              ‖ξ‖ ^ 4 *
                ‖h3RawProductConvolution
                  (W t k) (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      integrable_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun k _ =>
          integrable_finsetSum
            (Finset.univ : Finset (Fin 3))
            (fun j _ =>
              h3RawProductConvolution_selectedRestart_fourthMoment_integrable
                hν U₀ hA hU₀ ht htR k j))

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            (∑ k : Fin 3,
              ∑ j : Fin 3,
                ‖h3RawProductConvolution
                  (W t k) (W t j) ξ‖))
        (volume : Measure H3FourierPoint3) := by
    simpa only [Finset.mul_sum] using hMajorantExpanded

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3RawFinPressureFourier (W t) (W t) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      (continuous_norm.pow 4).aestronglyMeasurable.mul
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
      ‖ξ‖ ^ 4 *
          ‖∑ k : Fin 3,
              ∑ j : Fin 3,
                h3LerayRankOneCoefficient ξ j k *
                  h3RawProductConvolution
                    (W t k) (W t j) ξ‖
        ≤
      ‖ξ‖ ^ 4 *
        (∑ k : Fin 3,
          ∑ j : Fin 3,
            ‖h3RawProductConvolution
              (W t k) (W t j) ξ‖) :=
    mul_le_mul_of_nonneg_left
      hNorm
      (pow_nonneg (norm_nonneg ξ) 4)

  have hLeftNonneg :
      0 ≤
        ‖ξ‖ ^ 4 *
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

/-! ## Lower moments from L¹ plus the fourth moment -/

/-- Every natural radial weight through order four is bounded by
`1 + ‖ξ‖⁴`. -/
private theorem norm_pow_le_one_add_pow_four
    (ξ : H3FourierPoint3)
    (n : ℕ)
    (hn : n ≤ 4) :
    ‖ξ‖ ^ n ≤ 1 + ‖ξ‖ ^ 4 := by
  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ

  by_cases hx1 : ‖ξ‖ ≤ 1

  · have hpow :
        ‖ξ‖ ^ n ≤ (1 : ℝ) ^ n :=
      pow_le_pow_left₀ hx0 hx1 n

    have hpowOne :
        ‖ξ‖ ^ n ≤ 1 := by
      simpa using hpow

    exact
      hpowOne.trans
        (le_add_of_nonneg_right
          (pow_nonneg hx0 4))

  · have hx1' : 1 ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hx1)

    have hpow :
        ‖ξ‖ ^ n ≤ ‖ξ‖ ^ 4 :=
      pow_le_pow_right₀ hx1' hn

    exact
      le_add_of_nonneg_of_le
        zero_le_one
        hpow

/-- Selected pressure Fourier moments through order four are integrable. -/
theorem h3RawFinPressureFourier_selectedRestart_moment_integrable_four
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (n : ℕ)
    (hn : n ≤ 4) :
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

  let P : H3FourierPoint3 → ℂ :=
    h3RawFinPressureFourier (W t) (W t)

  have hP :
      Integrable P
        (volume : Measure H3FourierPoint3) := by
    dsimp only [P]
    exact
      h3RawFinPressureFourier_integrable
        (W t) (W t)

  have hP4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖P ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [P, W]
    exact
      h3RawFinPressureFourier_selectedRestart_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖P ξ‖ + ‖ξ‖ ^ 4 * ‖P ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hP.norm.add hP4

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ n * ‖P ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow n).aestronglyMeasurable.mul
      hP.norm.aestronglyMeasurable

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hWeight :=
    norm_pow_le_one_add_pow_four ξ n hn

  have hPoint :
      ‖ξ‖ ^ n * ‖P ξ‖
        ≤
      (1 + ‖ξ‖ ^ 4) * ‖P ξ‖ :=
    mul_le_mul_of_nonneg_right
      hWeight
      (norm_nonneg _)

  have hTarget0 :
      0 ≤ ‖ξ‖ ^ n * ‖P ξ‖ := by
    exact
      mul_nonneg
        (pow_nonneg (norm_nonneg ξ) n)
        (norm_nonneg (P ξ))

  have hPoint' :
      ‖ξ‖ ^ n * ‖P ξ‖
        ≤
      ‖P ξ‖ + ‖ξ‖ ^ 4 * ‖P ξ‖ := by
    calc
      ‖ξ‖ ^ n * ‖P ξ‖
          ≤
        (1 + ‖ξ‖ ^ 4) * ‖P ξ‖ :=
        hPoint
      _ =
        ‖P ξ‖ + ‖ξ‖ ^ 4 * ‖P ξ‖ := by
        ring

  change
    ‖(‖ξ‖ ^ n * ‖P ξ‖ : ℝ)‖
      ≤
    ‖P ξ‖ + ‖ξ‖ ^ 4 * ‖P ξ‖

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTarget0
  ] using hPoint'

/-! ## C4 reconstruction -/

/-- The canonical complex selected pressure reconstruction is spatially `C⁴`
at every strict positive restart time. -/
theorem h3RawFinPressureC1Representative_selectedRestart_contDiff_four
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
    ContDiff ℝ 4
      (h3RawFinPressureC1Representative
        (W t) (W t)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hFourier :
      ContDiff ℝ 4
        (FourierTransform.fourier
          (h3RawFinPressureFourier
            (W t) (W t))) := by
    apply Real.contDiff_fourier
    intro n hn

    have hn' : n ≤ 4 := by
      simpa using hn

    exact
      h3RawFinPressureFourier_selectedRestart_moment_integrable_four
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

/-- Taking real parts preserves selected pressure `C⁴`. -/
theorem h3RawFinPressureRealC1Representative_selectedRestart_contDiff_four
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
    ContDiff ℝ 4
      (h3RawFinPressureRealC1Representative
        (W t) (W t)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  unfold h3RawFinPressureRealC1Representative

  simpa [Function.comp_def] using
    (h3RawFinPressureC1Representative_selectedRestart_contDiff_four
      hν U₀ hA hU₀ ht htR).continuousLinearMap_comp
        Complex.reCLM

/-- Transport to `Point3` preserves selected pressure `C⁴`. -/
theorem h3RawFinPressureRealC1RepresentativeOnPoint3_selectedRestart_contDiff_four
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
    ContDiff ℝ 4
      (h3RawFinPressureRealC1RepresentativeOnPoint3
        (W t) (W t)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hPressure :
      ContDiff ℝ 4
        (h3RawFinPressureRealC1Representative
          (W t) (W t)) := by
    dsimp only [W]
    exact
      h3RawFinPressureRealC1Representative_selectedRestart_contDiff_four
        hν U₀ hA hU₀ ht htR

  have hToLp :
      ContDiff ℝ 4
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) := by
    exact PiLp.contDiff_toLp

  unfold h3RawFinPressureRealC1RepresentativeOnPoint3

  exact hPressure.comp hToLp

/-- Spacetime-path packaging: selected pressure is spatially `C⁴` at every
strict positive restart time. -/
theorem h3RawFinPressureRealC1OfPath_selectedRestart_contDiff_four
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
    ContDiff ℝ 4
      (h3RawFinPressureRealC1OfPath W t) := by
  dsimp only

  unfold h3RawFinPressureRealC1OfPath

  exact
    h3RawFinPressureRealC1RepresentativeOnPoint3_selectedRestart_contDiff_four
      hν U₀ hA hU₀ ht htR

/-- Exact `PressureSpatialC4OnTail` local shape: every first intrinsic
coordinate partial of selected pressure is spatially `C³`. -/
theorem h3RawFinPressureRealC1OfPath_selectedRestart_spatialDerivative_spatialC3
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    SpatialC3
      (spatial3.d i
        (h3RawFinPressureRealC1OfPath W t)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let p : ScalarField3 :=
    h3RawFinPressureRealC1OfPath W t

  have hp4 :
      ContDiff ℝ 4 p := by
    dsimp only [p, W]
    exact
      h3RawFinPressureRealC1OfPath_selectedRestart_contDiff_four
        hν U₀ hA hU₀ ht htR

  have hp3 :
      SpatialC3 p := by
    unfold SpatialC3
    exact hp4.of_le (by norm_num)

  change
    SpatialC3
      (fun x : Point3 =>
        partialDeriv i p x)

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_fun_eq
      hp3 i
  ]

  unfold SpatialC3

  exact
    (hp4.fderiv_right (by norm_num)).clm_apply
      contDiff_const

end

end Euclidean
end Bridge
end PrimeTensor
