import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.HeadGlobalProduct

/-!
# Global Fubini identification of the selected Duhamel head

`HeadGlobalProduct` proves genuine product integrability of the selected raw
retarded Fourier kernel on the midpoint head

    (0,t/2) × H3FourierPoint3.

The same inverse-Fourier phase used for the terminal tail has norm one, so it
preserves this product integrability.  Fubini therefore commutes source-time
integration with inverse Fourier reconstruction on the head interval.

This file introduces the explicit source-time-integrated head raw Fourier
amplitude and proves that its ordinary inverse Fourier transform is literally
the classical pointwise retarded `C³` integral over `0..t/2`.

No new estimate, endpoint argument, or quotient evaluation is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedHeadGlobalFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit source-time-integrated raw Fourier amplitude of the selected
midpoint head. -/
noncomputable def h3SelectedDuhamelHeadRawFourierAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ s in Set.Ioo (0 : ℝ) (t / 2),
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i (s, ξ)

/-- The explicit selected head raw Fourier amplitude is globally `L¹`. -/
theorem h3SelectedDuhamelHeadRawFourierAmplitude_integrable_global
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelHeadRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i)
      (volume : Measure H3FourierPoint3) := by
  have hProd :=
    h3SelectedDuhamelHeadComplexKernel_fubini_integrable_global
      hν U₀ hA hU₀ ht i

  have hOuter := hProd.integral_prod_right

  unfold h3SelectedDuhamelHeadRawFourierAmplitude
  exact hOuter

/-- Attaching the unit inverse-Fourier phase preserves product integrability
on the selected midpoint head. -/
theorem h3SelectedDuhamelHeadInverseFourierKernel_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Integrable
      (h3SelectedDuhamelTailInverseFourierKernel
        ν A t hν U₀ hA hU₀ i x)
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (t / 2))).prod
        (volume : Measure H3FourierPoint3)) := by
  have hBase :=
    h3SelectedDuhamelHeadComplexKernel_fubini_integrable_global
      hν U₀ hA hU₀ ht i

  have hPhase :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          𝐞 (-(inner ℝ p.2 (-x)))) := by
    fun_prop

  have hTargetMeas :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailInverseFourierKernel
          ν A t hν U₀ hA hU₀ i x)
        (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (t / 2))).prod
          (volume : Measure H3FourierPoint3)) := by
    unfold h3SelectedDuhamelTailInverseFourierKernel
    exact
      hPhase.aestronglyMeasurable.fun_smul
        (measurable_h3SelectedDuhamelTailComplexKernel
          hν U₀ hA hU₀ i).aestronglyMeasurable

  refine hBase.mono hTargetMeas ?_
  filter_upwards with p
  unfold h3SelectedDuhamelTailInverseFourierKernel
  simp only [Circle.norm_smul]
  exact le_rfl

/-- The inverse Fourier reconstruction of the explicit selected midpoint-head
raw amplitude is exactly the classical pointwise head Duhamel integral. -/
theorem h3SelectedDuhamelHeadFourierInv_eq_C3IntervalIntegral
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelHeadRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i)
        x
      =
    ∫ s in (0 : ℝ)..(t / 2),
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t W W i x s := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (t / 2))

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      h3SelectedDuhamelTailInverseFourierKernel
        ν A t hν U₀ hA hU₀ i x (s, ξ)

  have hFInt :
      Integrable
        (Function.uncurry F)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [Function.uncurry, F, μt]
    exact
      h3SelectedDuhamelHeadInverseFourierKernel_fubini_integrable
        hν U₀ hA hU₀ ht i x

  have hSwap :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            F s ξ
            ∂(volume : Measure H3FourierPoint3)
          ∂μt)
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s : ℝ,
          F s ξ
          ∂μt
        ∂(volume : Measure H3FourierPoint3) := by
    exact
      integral_integral_swap
        (μ := μt)
        (ν := (volume : Measure H3FourierPoint3))
        (f := F)
        hFInt

  have hhalf : 0 ≤ t / 2 := by
    linarith

  have hTimeSide :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            F s ξ
            ∂(volume : Measure H3FourierPoint3)
          ∂μt)
        =
      ∫ s in (0 : ℝ)..(t / 2),
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t W W i x s := by
    rw [intervalIntegral.integral_of_le hhalf]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    dsimp only [μt]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs

    unfold h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
    rw [
      h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel
    ]
    apply integral_congr_ae
    filter_upwards with ξ

    dsimp only [F]
    unfold
      h3SelectedDuhamelTailInverseFourierKernel
      h3SelectedDuhamelTailComplexKernel
      h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
    dsimp only [W]

  have hFrequencySide :
      (∫ ξ : H3FourierPoint3,
          ∫ s : ℝ,
            F s ξ
            ∂μt
          ∂(volume : Measure H3FourierPoint3))
        =
      FourierTransformInv.fourierInv
        (h3SelectedDuhamelHeadRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i)
        x := by
    symm
    rw [Real.fourierInv_eq_fourier_neg]
    rw [Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards with ξ

    unfold h3SelectedDuhamelHeadRawFourierAmplitude
    dsimp only [F, μt]
    unfold h3SelectedDuhamelTailInverseFourierKernel
    simp only [Circle.smul_def, smul_eq_mul]
    rw [← integral_const_mul]

  calc
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelHeadRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i)
        x
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s : ℝ,
          F s ξ
          ∂μt
        ∂(volume : Measure H3FourierPoint3) :=
      hFrequencySide.symm
    _ =
      ∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          F s ξ
          ∂(volume : Measure H3FourierPoint3)
        ∂μt :=
      hSwap.symm
    _ =
      ∫ s in (0 : ℝ)..(t / 2),
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t W W i x s :=
      hTimeSide

end

end Euclidean
end Bridge
end PrimeTensor
