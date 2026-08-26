import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Heat.Reality.L2.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weighted.Convolution.L2

/-!
# Hermitian reality of the weighted H³ product convolution

The heat part of the restart operator already preserves the deweighted
Hermitian Fourier condition.  The nonlinear velocity term begins with the
exact weighted product convolution

    W₃(ξ) ∫ f̂(η) ĝ(ξ - η) dη.

This file proves that this product step preserves the same reality condition.
The proof has three layers:

* transfer the packaged `L²` Hermitian hypothesis to the exact raw Fourier
  representative used in the convolution integral;
* use the volume-preserving substitution `η ↦ -η` and the fact that complex
  conjugation commutes with the Bochner integral to prove the raw convolution
  is Hermitian;
* cancel the exact H³ weight after reweighting, identifying the deweighted
  bundled output with the raw convolution almost everywhere.

The final theorem is the scalar nonlinear reality closure needed for the
finite outer-product tensor in the heat--Leray kernel.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SpectralConvolutionReality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact raw representatives -/

/-- The exact raw Fourier representative itself satisfies the Hermitian
relation almost everywhere whenever its packaged `L²` state does. -/
theorem h3SpectralScalarRawFourier_hermitian_ae
    {F : H3SpectralScalarState}
    (hF : H3SpectralScalarRawHermitian F) :
    ∀ᵐ ξ : H3FourierPoint3 ∂volume,
      h3SpectralScalarRawFourier F (-ξ)
        =
      conj (h3SpectralScalarRawFourier F ξ) := by
  unfold H3SpectralScalarRawHermitian H3FourierL2Hermitian at hF
  have hRaw := h3SpectralScalarRawFourierL2_ae F
  have hRawNeg := h3Fourier_ae_neg hRaw
  filter_upwards [hF, hRaw, hRawNeg] with ξ hHerm hAt hNeg
  calc
    h3SpectralScalarRawFourier F (-ξ)
        = h3SpectralScalarRawFourierL2 F (-ξ) := hNeg.symm
    _ = conj (h3SpectralScalarRawFourierL2 F ξ) := hHerm
    _ = conj (h3SpectralScalarRawFourier F ξ) := by rw [hAt]

/-! ## Hermitian symmetry of the raw convolution -/

/-- The exact raw scalar convolution of two Hermitian spectral states is
Hermitian at every output frequency. -/
theorem h3RawProductConvolution_hermitian
    {F G : H3SpectralScalarState}
    (hF : H3SpectralScalarRawHermitian F)
    (hG : H3SpectralScalarRawHermitian G)
    (ξ : H3FourierPoint3) :
    h3RawProductConvolution F G (-ξ)
      =
    conj (h3RawProductConvolution F G ξ) := by
  have hFraw := h3SpectralScalarRawFourier_hermitian_ae hF
  have hGraw := h3SpectralScalarRawFourier_hermitian_ae hG

  have hGshift :
      ∀ᵐ η : H3FourierPoint3 ∂volume,
        h3SpectralScalarRawFourier G (-(ξ - η))
          =
        conj (h3SpectralScalarRawFourier G (ξ - η)) := by
    exact
      (h3MeasurePreserving_sub_left ξ).quasiMeasurePreserving.ae hGraw

  have hConjIntegral :
      (∫ η : H3FourierPoint3,
          conj
            (h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)))
        =
      conj
        (∫ η : H3FourierPoint3,
          h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)) := by
    exact
      Complex.conjCLE.toContinuousLinearMap.integral_comp_comm
        (h3RawProductKernel_integrable F G ξ)

  unfold h3RawProductConvolution
  rw [← integral_neg_eq_self]
  calc
    (∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F (-η) *
          h3SpectralScalarRawFourier G (-ξ - -η))
        =
      ∫ η : H3FourierPoint3,
        conj
          (h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)) := by
          apply integral_congr_ae
          filter_upwards [hFraw, hGshift] with η hFη hGη
          rw [hFη]
          rw [show -ξ - -η = -(ξ - η) by abel, hGη]
          simp only [map_mul]
    _ =
      conj
        (∫ η : H3FourierPoint3,
          h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)) := hConjIntegral

/-! ## Cancellation of the weighted output -/

/-- Deweighting the bundled weighted product convolution recovers the exact
raw convolution almost everywhere. -/
theorem h3SpectralScalarRawFourierL2_weightedRawProductConvolutionL2_ae
    (F G : H3SpectralScalarState) :
    (h3SpectralScalarRawFourierL2
        (h3WeightedRawProductConvolutionL2 F G) :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    h3RawProductConvolution F G := by
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae
      (h3WeightedRawProductConvolutionL2 F G),
    h3WeightedRawProductConvolutionL2_ae F G
  ] with ξ hRaw hWeighted
  rw [hRaw]
  unfold h3SpectralScalarRawFourier
  rw [hWeighted]
  unfold h3WeightedRawProductConvolution
  rw [← mul_assoc,
    h3SobolevFrequencyWeightInvComplex_mul_weight,
    one_mul]

/-- The genuine weighted H³ product convolution preserves the deweighted
Hermitian Fourier reality condition. -/
theorem h3WeightedRawProductConvolutionL2_preserves_rawHermitian
    {F G : H3SpectralScalarState}
    (hF : H3SpectralScalarRawHermitian F)
    (hG : H3SpectralScalarRawHermitian G) :
    H3SpectralScalarRawHermitian
      (h3WeightedRawProductConvolutionL2 F G) := by
  unfold H3SpectralScalarRawHermitian H3FourierL2Hermitian
  have hOut :=
    h3SpectralScalarRawFourierL2_weightedRawProductConvolutionL2_ae F G
  have hOutNeg := h3Fourier_ae_neg hOut
  filter_upwards [hOut, hOutNeg] with ξ hAt hNeg
  rw [hNeg, hAt]
  exact h3RawProductConvolution_hermitian hF hG ξ

/-! ## Finite outer-product lift -/

/-- Coordinatewise Hermitian reality for a finite spectral tensor state. -/
def H3SpectralFinTensorRawHermitian
    (T : H3SpectralFinTensorState) : Prop :=
  ∀ i j : Fin 3, H3SpectralScalarRawHermitian (T i j)

/-- The finite weighted spectral outer product of two Hermitian velocity
states is a Hermitian tensor state. -/
theorem h3SpectralFinOuterProduct_preserves_rawHermitian
    {U V : H3SpectralFinVectorState}
    (hU : H3SpectralVelocityRawHermitian U)
    (hV : H3SpectralVelocityRawHermitian V) :
    H3SpectralFinTensorRawHermitian
      (h3SpectralFinOuterProduct U V) := by
  intro i j
  change
    H3SpectralScalarRawHermitian
      (h3WeightedRawProductConvolutionL2 (U i) (V j))
  exact
    h3WeightedRawProductConvolutionL2_preserves_rawHermitian
      (hU i) (hV j)

end

end Euclidean
end Bridge
end PrimeTensor
