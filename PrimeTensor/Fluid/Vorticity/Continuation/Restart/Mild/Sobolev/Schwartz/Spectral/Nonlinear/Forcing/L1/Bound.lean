import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Endpoint.Time.Kernel

/-!
# Quantitative Fourier L¹ bound for the unheated nonlinear forcing

The previous endpoint modules prove that the complete unheated finite-index
Leray--divergence forcing is Fourier `L¹`, and that positive heat lag turns its
first Fourier moment into a `τ⁻¹/²` singularity.  To integrate that estimate
along a Duhamel path we also need a *uniform quantitative bound* on the
unheated Fourier `L¹` mass in terms of the H³ norms of the two input states.

This file obtains that bound without new harmonic analysis.

First we package

    ξ ↦ ‖ξ‖ W₃(ξ)⁻¹

as a genuine complex `L²` multiplier.  Hölder then gives the quantitative
first-moment deweighting estimate

    ∫ ‖ξ‖ |f̂(ξ)| dξ ≤ C₁ ‖W₃ f̂‖₂.

Applying this to the already-bundled weighted H³ product convolution and then
using the scalar H³ algebra estimate controls the first moment of the exact
raw product convolution.  One Fourier derivative costs `2π`, the finite
three-term divergence costs a factor `3`, and the finite Leray matrix costs a
factor `6`.

The result is a reusable bilinear estimate

    mass(P div(U⊗V)) ≤ C_force ‖U‖ ‖V‖.

This is the missing frequency-side majorant for the short Duhamel tail.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingL1Bound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Quantitative first-moment deweighting -/

/-- Complex-valued copy of the first-moment reciprocal H³ weight. -/
def h3SobolevFrequencyFirstMomentInvComplex
    (ξ : H3FourierPoint3) : ℂ :=
  h3SobolevFrequencyFirstMomentInv ξ

/-- The complex first-moment reciprocal weight belongs to `L²`. -/
theorem h3SobolevFrequencyFirstMomentInvComplex_memLp2 :
    MemLp
      h3SobolevFrequencyFirstMomentInvComplex
      2
      (volume : Measure H3FourierPoint3) := by
  exact h3SobolevFrequencyFirstMomentInv_memLp2.ofReal

/-- The first-moment reciprocal H³ weight as a genuine complex `L²` state. -/
noncomputable def h3SobolevFrequencyFirstMomentInvComplexL2 :
    H3FourierComplexL2 :=
  h3SobolevFrequencyFirstMomentInvComplex_memLp2.toLp
    h3SobolevFrequencyFirstMomentInvComplex

/-- The packaged first-moment multiplier has the expected representative. -/
theorem h3SobolevFrequencyFirstMomentInvComplexL2_ae :
    (h3SobolevFrequencyFirstMomentInvComplexL2 :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    h3SobolevFrequencyFirstMomentInvComplex := by
  exact
    MemLp.coeFn_toLp
      h3SobolevFrequencyFirstMomentInvComplex_memLp2

/-- Fixed H³-to-first-Fourier-moment embedding constant. -/
def h3SobolevFirstMomentDeweightingConstant : ℝ :=
  ‖h3SobolevFrequencyFirstMomentInvComplexL2‖

/-- The first-moment deweighting constant is nonnegative. -/
theorem h3SobolevFirstMomentDeweightingConstant_nonneg :
    0 ≤ h3SobolevFirstMomentDeweightingConstant := by
  unfold h3SobolevFirstMomentDeweightingConstant
  exact norm_nonneg _

/-- Hölder-packaged first raw Fourier moment of a weighted H³ state. -/
noncomputable def h3SpectralScalarRawFourierFirstMomentHolderL1
    (G : H3SpectralScalarState) :
    H3FourierComplexL1 :=
  h3SobolevFrequencyFirstMomentInvComplexL2 • G

/-- Quantitative first-moment deweighting bound. -/
theorem norm_h3SpectralScalarRawFourierFirstMomentHolderL1_le
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarRawFourierFirstMomentHolderL1 G‖
      ≤
    h3SobolevFirstMomentDeweightingConstant * ‖G‖ := by
  unfold
    h3SpectralScalarRawFourierFirstMomentHolderL1
    h3SobolevFirstMomentDeweightingConstant
  exact
    MeasureTheory.Lp.norm_smul_le
      h3SobolevFrequencyFirstMomentInvComplexL2 G

/-- The Hölder package represents `‖ξ‖ f̂(ξ)` almost everywhere. -/
theorem h3SpectralScalarRawFourierFirstMomentHolderL1_ae
    (G : H3SpectralScalarState) :
    (h3SpectralScalarRawFourierFirstMomentHolderL1 G :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      (‖ξ‖ : ℂ) * h3SpectralScalarRawFourier G ξ) := by
  have hMul :
      (h3SpectralScalarRawFourierFirstMomentHolderL1 G :
          H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      ((h3SobolevFrequencyFirstMomentInvComplexL2 :
          H3FourierPoint3 → ℂ) •
        (G : H3FourierPoint3 → ℂ)) := by
    simpa [h3SpectralScalarRawFourierFirstMomentHolderL1] using
      (MeasureTheory.Lp.coeFn_lpSMul
        (r := (1 : ENNReal))
        h3SobolevFrequencyFirstMomentInvComplexL2 G)

  filter_upwards [
    hMul,
    h3SobolevFrequencyFirstMomentInvComplexL2_ae
  ] with ξ hMulξ hInvξ

  rw [hMulξ]
  simp only [Pi.smul_apply', smul_eq_mul]
  rw [hInvξ]
  unfold
    h3SobolevFrequencyFirstMomentInvComplex
    h3SobolevFrequencyFirstMomentInv
    h3SpectralScalarRawFourier
    h3SobolevFrequencyWeightInvComplex
  simp only [Pi.smul_apply', smul_eq_mul, Complex.ofReal_mul]
  ring

/-- Quantitative first raw Fourier moment bound for every weighted H³ scalar
state. -/
theorem h3SpectralScalarRawFourier_firstMoment_integral_le
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖)
      ≤
    h3SobolevFirstMomentDeweightingConstant * ‖G‖ := by
  have hNormEq :
      ‖h3SpectralScalarRawFourierFirstMomentHolderL1 G‖
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [
      h3SpectralScalarRawFourierFirstMomentHolderL1_ae G
    ] with ξ hξ
    rw [hξ, norm_mul]
    simp

  rw [← hNormEq]
  exact norm_h3SpectralScalarRawFourierFirstMomentHolderL1_le G

/-! ## Product-convolution and derivative bounds -/

/-- Quantitative first-moment bound for the exact raw convolution of two H³
states. -/
theorem h3RawProductConvolution_firstMoment_integral_le
    (F G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖h3RawProductConvolution F G ξ‖)
      ≤
    h3SobolevFirstMomentDeweightingConstant *
      (16 * h3SobolevDeweightingConstant * ‖F‖ * ‖G‖) := by
  let P : H3SpectralScalarState :=
    h3WeightedRawProductConvolutionL2 F G

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ * ‖h3RawProductConvolution F G ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
          ‖ξ‖ * ‖h3SpectralScalarRawFourier P ξ‖ := by
    apply integral_congr_ae
    filter_upwards [
      h3SpectralScalarRawFourier_weightedRawProductConvolutionL2_ae F G
    ] with ξ hξ
    rw [hξ]

  rw [hIntegralEq]
  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖h3SpectralScalarRawFourier P ξ‖)
        ≤
      h3SobolevFirstMomentDeweightingConstant * ‖P‖ :=
        h3SpectralScalarRawFourier_firstMoment_integral_le P
    _ ≤
      h3SobolevFirstMomentDeweightingConstant *
        (16 * h3SobolevDeweightingConstant * ‖F‖ * ‖G‖) := by
          exact
            mul_le_mul_of_nonneg_left
              (norm_h3WeightedRawProductConvolutionL2_le F G)
              h3SobolevFirstMomentDeweightingConstant_nonneg

/-- Fixed coefficient for one differentiated raw product convolution. -/
def h3RawProductDerivativeL1Coefficient : ℝ :=
  (2 * Real.pi) * h3SobolevFirstMomentDeweightingConstant *
    (16 * h3SobolevDeweightingConstant)

/-- The differentiated-product `L¹` coefficient is nonnegative. -/
theorem h3RawProductDerivativeL1Coefficient_nonneg :
    0 ≤ h3RawProductDerivativeL1Coefficient := by
  unfold h3RawProductDerivativeL1Coefficient
  positivity [
    h3SobolevFirstMomentDeweightingConstant_nonneg,
    h3SobolevDeweightingConstant_nonneg
  ]

/-- Quantitative `L¹` bound after spending one raw Fourier moment on one
spatial divergence derivative. -/
theorem h3FourierDerivative_mul_rawProductConvolution_norm_integral_le
    (F G : H3SpectralScalarState)
    (j : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ‖)
      ≤
    h3RawProductDerivativeL1Coefficient * ‖F‖ * ‖G‖ := by
  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3FourierDerivative_mul_rawProductConvolution_integrable F G j).norm

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3RawProductConvolution_firstMoment_integrable F G

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ * ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul (2 * Real.pi)

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (‖ξ‖ * ‖h3RawProductConvolution F G ξ‖) := by
            refine integral_mono_ae hTargetInt hMajorantInt ?_
            filter_upwards with ξ
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
    _ =
      (2 * Real.pi) *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ * ‖h3RawProductConvolution F G ξ‖) := by
            rw [integral_const_mul]
    _ ≤
      (2 * Real.pi) *
        (h3SobolevFirstMomentDeweightingConstant *
          (16 * h3SobolevDeweightingConstant * ‖F‖ * ‖G‖)) := by
            exact
              mul_le_mul_of_nonneg_left
                (h3RawProductConvolution_firstMoment_integral_le F G)
                (by positivity)
    _ =
      h3RawProductDerivativeL1Coefficient * ‖F‖ * ‖G‖ := by
        unfold h3RawProductDerivativeL1Coefficient
        ring

/-! ## Finite divergence and Leray bounds -/

/-- The raw three-term outer-product divergence has quantitative Fourier
`L¹` mass controlled by the two finite-vector H³ norms. -/
theorem h3RawFinOuterProductDivergence_norm_integral_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinOuterProductDivergence U V i ξ‖)
      ≤
    3 * h3RawProductDerivativeL1Coefficient * ‖U‖ * ‖V‖ := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ =>
      h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U i) (V j) ξ

  have hTermInt :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 => ‖term j ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp [term]
    exact
      (h3FourierDerivative_mul_rawProductConvolution_integrable
        (U i) (V j) j).norm

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ j : Fin 3, ‖term j ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      integrable_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun j _ => hTermInt j)

  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinOuterProductDivergence_integrable U V i).norm

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ j : Fin 3, ‖term j ξ‖ := by
          refine integral_mono_ae hTargetInt hMajorantInt ?_
          filter_upwards with ξ
          unfold h3RawFinOuterProductDivergence
          dsimp [term]
          exact
            norm_sum_le
              Finset.univ
              (fun j : Fin 3 =>
                h3FourierDerivativeSymbol j ξ *
                  h3RawProductConvolution (U i) (V j) ξ)
    _ =
      ∑ j : Fin 3,
        ∫ ξ : H3FourierPoint3, ‖term j ξ‖ := by
          simpa using
            (integral_finsetSum (μ := volume) Finset.univ
              (fun j _ => hTermInt j))
    _ ≤
      ∑ j : Fin 3,
        h3RawProductDerivativeL1Coefficient * ‖U i‖ * ‖V j‖ := by
          exact
            Finset.sum_le_sum
              (fun j _ => by
                dsimp [term]
                exact
                  h3FourierDerivative_mul_rawProductConvolution_norm_integral_le
                    (U i) (V j) j)
    _ ≤
      ∑ _j : Fin 3,
        h3RawProductDerivativeL1Coefficient * ‖U‖ * ‖V‖ := by
          exact
            Finset.sum_le_sum
              (fun j _ => by
                have hUi := h3SpectralFinVector_coordinate_norm_le U i
                have hVj := h3SpectralFinVector_coordinate_norm_le V j
                have hC := h3RawProductDerivativeL1Coefficient_nonneg
                calc
                  h3RawProductDerivativeL1Coefficient * ‖U i‖ * ‖V j‖
                      ≤
                    h3RawProductDerivativeL1Coefficient * ‖U‖ * ‖V j‖ := by
                      exact
                        mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left hUi hC)
                          (norm_nonneg (V j))
                  _ ≤
                    h3RawProductDerivativeL1Coefficient * ‖U‖ * ‖V‖ := by
                      exact
                        mul_le_mul_of_nonneg_left
                          hVj
                          (mul_nonneg hC (norm_nonneg U)))
    _ =
      3 * h3RawProductDerivativeL1Coefficient * ‖U‖ * ‖V‖ := by
        simp
        ring

/-- Fixed bilinear Fourier-`L¹` coefficient for the complete unheated
finite-index Leray--divergence forcing. -/
def h3NonlinearForcingL1Coefficient : ℝ :=
  18 * h3RawProductDerivativeL1Coefficient

/-- The complete nonlinear forcing coefficient is nonnegative. -/
theorem h3NonlinearForcingL1Coefficient_nonneg :
    0 ≤ h3NonlinearForcingL1Coefficient := by
  unfold h3NonlinearForcingL1Coefficient
  exact
    mul_nonneg
      (by norm_num)
      h3RawProductDerivativeL1Coefficient_nonneg

/-- Quantitative Fourier `L¹` mass bound for one output coordinate of the
complete unheated finite-index Leray--divergence forcing. -/
theorem h3RawFinLerayOuterProductDivergenceL1Mass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceL1Mass U V i
      ≤
    h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V‖ := by
  let divTerm : Fin 3 → H3FourierPoint3 → ℂ :=
    fun k ξ => h3RawFinOuterProductDivergence U V k ξ

  have hDivInt :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 => ‖divTerm k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp [divTerm]
    exact (h3RawFinOuterProductDivergence_integrable U V k).norm

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ k : Fin 3, 2 * ‖divTerm k ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      integrable_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun k _ => (hDivInt k).const_mul 2)

  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergence_integrable U V i).norm

  unfold h3RawFinLerayOuterProductDivergenceL1Mass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ k : Fin 3, 2 * ‖divTerm k ξ‖ := by
          refine integral_mono_ae hTargetInt hMajorantInt ?_
          filter_upwards with ξ
          unfold h3RawFinLerayOuterProductDivergence
          calc
            ‖∑ k : Fin 3,
                h3LerayCoefficient ξ i k * divTerm k ξ‖
                ≤
              ∑ k : Fin 3,
                ‖h3LerayCoefficient ξ i k * divTerm k ξ‖ := by
                  exact
                    norm_sum_le
                      Finset.univ
                      (fun k : Fin 3 =>
                        h3LerayCoefficient ξ i k * divTerm k ξ)
            _ ≤
              ∑ k : Fin 3, 2 * ‖divTerm k ξ‖ := by
                exact
                  Finset.sum_le_sum
                    (fun k _ => by
                      rw [norm_mul]
                      exact
                        mul_le_mul_of_nonneg_right
                          (norm_h3LerayCoefficient_le_two ξ i k)
                          (norm_nonneg _))
    _ =
      ∑ k : Fin 3,
        ∫ ξ : H3FourierPoint3, 2 * ‖divTerm k ξ‖ := by
          simpa using
            (integral_finsetSum (μ := volume) Finset.univ
              (fun k _ => (hDivInt k).const_mul 2))
    _ =
      ∑ k : Fin 3,
        2 * (∫ ξ : H3FourierPoint3, ‖divTerm k ξ‖) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [integral_const_mul]
    _ ≤
      ∑ _k : Fin 3,
        2 * (3 * h3RawProductDerivativeL1Coefficient * ‖U‖ * ‖V‖) := by
          exact
            Finset.sum_le_sum
              (fun k _ =>
                mul_le_mul_of_nonneg_left
                  (h3RawFinOuterProductDivergence_norm_integral_le U V k)
                  (by norm_num))
    _ =
      h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V‖ := by
        unfold h3NonlinearForcingL1Coefficient
        simp
        ring

end

end Euclidean
end Bridge
end PrimeTensor
