import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.GlobalProduct
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Time.Integrability

/-!
# Global Fubini identification of the selected terminal Duhamel tail

`GlobalProduct` proves that the unweighted selected terminal-half raw Fourier
kernel is genuinely integrable on the full source-time/frequency product.

That is exactly the hypothesis needed to commute inverse Fourier
reconstruction with the terminal-half source-time integral.

For a fixed spatial point `x`, multiply the raw kernel by the unit Fourier
phase

    𝐞 (-(⟪ξ,-x⟫)).

The phase has norm one, so product integrability is unchanged.  Fubini then
swaps the source-time and frequency integrals.

* Frequency first gives the classical positive-lag `C³` retarded path.
* Source time first gives the inverse Fourier transform of the selected raw
  terminal-tail amplitude.

Thus the inverse Fourier reconstruction of the selected terminal-tail raw
amplitude is literally the classical pointwise terminal-tail Duhamel
integral.

No quotient evaluation and no new analytic estimate are introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailGlobalFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected terminal-tail raw Fourier amplitude is globally `L¹` once the
restart-radius endpoint estimates are available. -/
theorem h3SelectedDuhamelTailRawFourierAmplitude_integrable_global
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i)
      (volume : Measure H3FourierPoint3) := by
  have hProd :=
    h3SelectedDuhamelTailComplexKernel_fubini_integrable_global
      hν U₀ hA hU₀ ht htR i

  have hOuter := hProd.integral_prod_right

  unfold h3SelectedDuhamelTailRawFourierAmplitude
  exact hOuter

/-- Product kernel obtained by attaching the inverse-Fourier phase at a fixed
spatial point to the selected terminal-tail raw kernel. -/
noncomputable def h3SelectedDuhamelTailInverseFourierKernel
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (p : ℝ × H3FourierPoint3) : ℂ :=
  𝐞 (-(inner ℝ p.2 (-x))) •
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i p

/-- Attaching the unit inverse-Fourier phase preserves global product
integrability of the selected terminal-tail kernel. -/
theorem h3SelectedDuhamelTailInverseFourierKernel_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Integrable
      (h3SelectedDuhamelTailInverseFourierKernel
        ν A t hν U₀ hA hU₀ i x)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        (volume : Measure H3FourierPoint3)) := by
  have hBase :=
    h3SelectedDuhamelTailComplexKernel_fubini_integrable_global
      hν U₀ hA hU₀ ht htR i

  have hPhase :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          𝐞 (-(inner ℝ p.2 (-x)))) := by
    fun_prop

  have hTargetMeas :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailInverseFourierKernel
          ν A t hν U₀ hA hU₀ i x)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
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

/-- The inverse Fourier reconstruction of the selected terminal-half raw
amplitude is exactly the classical pointwise terminal-half Duhamel integral. -/
theorem h3SelectedDuhamelTailFourierInv_eq_C3IntervalIntegral
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelTailRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i)
        x
      =
    ∫ s in (t / 2)..t,
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t W W i x s := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

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
      h3SelectedDuhamelTailInverseFourierKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i x

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

  have hhalf : t / 2 ≤ t := by
    linarith

  have hTimeSide :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            F s ξ
            ∂(volume : Measure H3FourierPoint3)
          ∂μt)
        =
      ∫ s in (t / 2)..t,
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
        (h3SelectedDuhamelTailRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i)
        x := by
    symm
    rw [Real.fourierInv_eq_fourier_neg]
    rw [Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards with ξ

    unfold h3SelectedDuhamelTailRawFourierAmplitude
    dsimp only [F, μt]
    unfold h3SelectedDuhamelTailInverseFourierKernel
    simp only [Circle.smul_def, smul_eq_mul]
    rw [← integral_const_mul]

  calc
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelTailRawFourierAmplitude
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
      ∫ s in (t / 2)..t,
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t W W i x s :=
      hTimeSide

end

end Euclidean
end Bridge
end PrimeTensor
