import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralH3RealC1Bridge

/-!
# Fourier L¹ control of the unheated H³ nonlinear forcing

`SchwartzSpectralH3RealC1Bridge` proves that the deweighted Fourier amplitude
of every weighted H³ scalar state has integrable moments through order one.
The H³ algebra theorem already packages a pointwise product as the weighted
spectral state

    W₃(ξ) (f̂ * ĝ)(ξ).

Therefore its deweighted representative is the exact raw convolution and
inherits the same zeroth- and first-moment `L¹` control.

This file records that identification and then spends the first raw moment on
the single divergence derivative.  Since every finite Leray coefficient is a
bounded measurable multiplier, the complete *unheated* finite-index
Leray-divergence forcing is Fourier `L¹` coordinatewise.

This is the endpoint bootstrap datum for the singular Duhamel tail: heat is
no longer needed merely to make the nonlinear forcing an integrable Fourier
amplitude.  Further spatial gains can now be proved by combining this `L¹`
forcing with the positive heat lag inside the retarded integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingL1
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Raw product convolution moments -/

/-- Deweighting the bundled weighted H³ product recovers the exact raw
convolution almost everywhere. -/
theorem h3SpectralScalarRawFourier_weightedRawProductConvolutionL2_ae
    (F G : H3SpectralScalarState) :
    h3SpectralScalarRawFourier
        (h3WeightedRawProductConvolutionL2 F G)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3RawProductConvolution F G := by
  filter_upwards [
    h3WeightedRawProductConvolutionL2_ae F G
  ] with ξ hξ
  unfold h3SpectralScalarRawFourier
  rw [hξ]
  unfold h3WeightedRawProductConvolution
  rw [← mul_assoc,
    h3SobolevFrequencyWeightInvComplex_mul_weight,
    one_mul]

/-- The exact raw Fourier convolution of two H³ states is integrable. -/
theorem h3RawProductConvolution_integrable
    (F G : H3SpectralScalarState) :
    Integrable
      (h3RawProductConvolution F G)
      (volume : Measure H3FourierPoint3) := by
  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier
          (h3WeightedRawProductConvolutionL2 F G))
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1
        (h3WeightedRawProductConvolutionL2 F G))
  exact
    hRaw.congr
      (h3SpectralScalarRawFourier_weightedRawProductConvolutionL2_ae F G)

/-- The first raw Fourier moment of the exact H³ product convolution is
integrable. -/
theorem h3RawProductConvolution_firstMoment_integrable
    (F G : H3SpectralScalarState) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ * ‖h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hMoment :=
    h3SpectralScalarRawFourier_firstMoment_integrable
      (h3WeightedRawProductConvolutionL2 F G)
  refine hMoment.congr ?_
  filter_upwards [
    h3SpectralScalarRawFourier_weightedRawProductConvolutionL2_ae F G
  ] with ξ hξ
  rw [hξ]

/-- Raw product-convolution moments through order one are integrable. -/
theorem h3RawProductConvolution_moment_integrable_one
    (F G : H3SpectralScalarState)
    (n : ℕ)
    (hn : n ≤ 1) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ n * ‖h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hnCases : n = 0 ∨ n = 1 := by omega
  rcases hnCases with rfl | rfl
  · simpa using (h3RawProductConvolution_integrable F G).norm
  · simpa using h3RawProductConvolution_firstMoment_integrable F G

/-! ## Spending the first moment on one divergence derivative -/

/-- One Fourier divergence derivative of an exact H³ product convolution is
still integrable. -/
theorem h3FourierDerivative_mul_rawProductConvolution_integrable
    (F G : H3SpectralScalarState)
    (j : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ)
      (volume : Measure H3FourierPoint3) := by
  let P : H3SpectralScalarState :=
    h3WeightedRawProductConvolutionL2 F G

  have hConvAE :
      h3SpectralScalarRawFourier P
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawProductConvolution F G := by
    dsimp [P]
    exact h3SpectralScalarRawFourier_weightedRawProductConvolutionL2_ae F G

  have hConvMeas :
      AEStronglyMeasurable
        (h3RawProductConvolution F G)
        (volume : Measure H3FourierPoint3) := by
    exact
      (h3SpectralScalarRawFourier_memLp1 P).1.congr hConvAE

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (h3FourierDerivativeSymbol_continuous j).aestronglyMeasurable.mul
        hConvMeas

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ * ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) := by
    exact
      (h3RawProductConvolution_firstMoment_integrable F G).const_mul
        (2 * Real.pi)

  refine Integrable.mono' hMajorant hTargetMeas ?_
  filter_upwards with ξ

  have hTwoPi : 0 ≤ 2 * Real.pi := by positivity
  have hMomentNonneg :
      0 ≤ ‖ξ‖ * ‖h3RawProductConvolution F G ξ‖ := by
    positivity
  have hMajorantNonneg :
      0 ≤
        (2 * Real.pi) *
          (‖ξ‖ * ‖h3RawProductConvolution F G ξ‖) :=
    mul_nonneg hTwoPi hMomentNonneg

  have hBound :
      ‖h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ‖
        ≤
      (2 * Real.pi) *
        (‖ξ‖ * ‖h3RawProductConvolution F G ξ‖) := by
    calc
      ‖h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ‖
          =
        ‖h3FourierDerivativeSymbol j ξ‖ *
          ‖h3RawProductConvolution F G ξ‖ := by
            rw [norm_mul]
      _ ≤
        h3FourierGradientMagnitude ξ *
          ‖h3RawProductConvolution F G ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ)
          (norm_nonneg _)
      _ =
        (2 * Real.pi) *
          (‖ξ‖ * ‖h3RawProductConvolution F G ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

  simpa [Real.norm_eq_abs, abs_of_nonneg hMajorantNonneg] using hBound

/-! ## Finite divergence and Leray forcing -/

/-- Raw unheated divergence of the exact finite-index H³ outer product. -/
noncomputable def h3RawFinOuterProductDivergence
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∑ j : Fin 3,
    h3FourierDerivativeSymbol j ξ *
      h3RawProductConvolution (U i) (V j) ξ

/-- Every output coordinate of the raw unheated outer-product divergence is
Fourier `L¹`. -/
theorem h3RawFinOuterProductDivergence_integrable
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    Integrable
      (h3RawFinOuterProductDivergence U V i)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawFinOuterProductDivergence
  simpa using
    (integrable_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun j _ =>
        h3FourierDerivative_mul_rawProductConvolution_integrable
          (U i) (V j) j))

/-- Apply the finite Fourier Leray matrix to the raw outer-product divergence. -/
noncomputable def h3RawFinLerayOuterProductDivergence
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∑ k : Fin 3,
    h3LerayCoefficient ξ i k *
      h3RawFinOuterProductDivergence U V k ξ

/-- A bounded Leray entry preserves integrability of one raw divergence
coordinate. -/
theorem h3LerayCoefficient_mul_rawFinOuterProductDivergence_integrable
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3LerayCoefficient ξ i k *
          h3RawFinOuterProductDivergence U V k ξ)
      (volume : Measure H3FourierPoint3) := by
  have hDiv := h3RawFinOuterProductDivergence_integrable U V k

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (measurable_h3LerayCoefficient i k).aestronglyMeasurable.mul
        hDiv.1

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 * ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact hDiv.norm.const_mul 2

  refine Integrable.mono' hMajorant hTargetMeas ?_
  filter_upwards with ξ

  have hDivNonneg :
      0 ≤ 2 * ‖h3RawFinOuterProductDivergence U V k ξ‖ := by
    positivity

  have hBound :
      ‖h3LerayCoefficient ξ i k *
          h3RawFinOuterProductDivergence U V k ξ‖
        ≤
      2 * ‖h3RawFinOuterProductDivergence U V k ξ‖ := by
    rw [norm_mul]
    exact
      mul_le_mul_of_nonneg_right
        (norm_h3LerayCoefficient_le_two ξ i k)
        (norm_nonneg _)

  simpa [Real.norm_eq_abs, abs_of_nonneg hDivNonneg] using hBound

/-- The complete unheated finite-index Leray-divergence forcing generated by
two H³ velocity states is Fourier `L¹` coordinatewise. -/
theorem h3RawFinLerayOuterProductDivergence_integrable
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    Integrable
      (h3RawFinLerayOuterProductDivergence U V i)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawFinLerayOuterProductDivergence
  simpa using
    (integrable_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun k _ =>
        h3LerayCoefficient_mul_rawFinOuterProductDivergence_integrable
          U V i k))

end

end Euclidean
end Bridge
end PrimeTensor
