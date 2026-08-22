import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.YoungConvolution
import Mathlib.MeasureTheory.Function.Holder

/-!
# Quantitative H³ deweighting and the weighted convolution kernel

`YoungConvolution` gives the endpoint estimate

    L¹ * L² → L².

To use it for the H³ product estimate we need two further facts.

First, deweighting a spectral H³ state is not merely in `L¹`; its `L¹` norm
is quantitatively controlled by the H³ spectral norm.  We package the inverse
Sobolev weight as an `L²` function and use Hölder in the bundled `Lp` spaces.

Second, the exact H³ weight split gives the pointwise kernel inequality

    W₃(ξ) |f̂(η) ĝ(ξ-η)|
      ≤ 8 (
          |W₃(η) f̂(η)| |ĝ(ξ-η)|
          + |f̂(η)| |W₃(ξ-η) ĝ(ξ-η)|).

This file proves precisely those two ingredients without yet identifying the
weighted product with a Bochner convolution.  The next step is the
change-of-variables / Bochner assembly that turns this kernel estimate and the
endpoint Young theorem into the H³ algebra bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SobolevAlgebra
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Quantitative deweighting -/

/-- The inverse exact H³ weight, packaged as a complex `L²` function. -/
noncomputable def h3SobolevFrequencyWeightInvComplexL2 :
    H3FourierComplexL2 :=
  h3SobolevFrequencyWeightInvComplex_memLp2.toLp
    h3SobolevFrequencyWeightInvComplex

/-- The packaged inverse weight has the expected representative a.e. -/
theorem h3SobolevFrequencyWeightInvComplexL2_ae :
    (h3SobolevFrequencyWeightInvComplexL2 :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    h3SobolevFrequencyWeightInvComplex := by
  exact
    MemLp.coeFn_toLp
      h3SobolevFrequencyWeightInvComplex_memLp2

/-- The fixed Sobolev-to-Fourier-`L¹` embedding constant. -/
def h3SobolevDeweightingConstant : ℝ :=
  ‖h3SobolevFrequencyWeightInvComplexL2‖

/-- The deweighting constant is nonnegative. -/
theorem h3SobolevDeweightingConstant_nonneg :
    0 ≤ h3SobolevDeweightingConstant := by
  unfold h3SobolevDeweightingConstant
  exact norm_nonneg _

/--
Canonical bundled `L¹` raw Fourier amplitude obtained by Hölder multiplication
of the inverse H³ weight with a weighted spectral state.
-/
noncomputable def h3SpectralScalarRawFourierHolderL1
    (G : H3SpectralScalarState) :
    H3FourierComplexL1 :=
  h3SobolevFrequencyWeightInvComplexL2 • G

/-- Quantitative `H³ → Fourier L¹` deweighting bound. -/
theorem norm_h3SpectralScalarRawFourierHolderL1_le
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarRawFourierHolderL1 G‖
      ≤
    h3SobolevDeweightingConstant * ‖G‖ := by
  unfold
    h3SpectralScalarRawFourierHolderL1
    h3SobolevDeweightingConstant
  exact
    MeasureTheory.Lp.norm_smul_le
      h3SobolevFrequencyWeightInvComplexL2 G

/--
The Hölder-packaged `L¹` state represents the previously defined raw Fourier
amplitude almost everywhere.
-/
theorem h3SpectralScalarRawFourierHolderL1_ae
    (G : H3SpectralScalarState) :
    (h3SpectralScalarRawFourierHolderL1 G :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    h3SpectralScalarRawFourier G := by
  have hMul :
      (h3SpectralScalarRawFourierHolderL1 G :
          H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      ((h3SobolevFrequencyWeightInvComplexL2 :
          H3FourierPoint3 → ℂ) •
        (G : H3FourierPoint3 → ℂ)) := by
    simpa [h3SpectralScalarRawFourierHolderL1] using
      (MeasureTheory.Lp.coeFn_lpSMul
        (r := (1 : ENNReal))
        h3SobolevFrequencyWeightInvComplexL2 G)
  filter_upwards [
    hMul,
    h3SobolevFrequencyWeightInvComplexL2_ae
  ] with ξ hMulξ hInvξ
  rw [hMulξ]
  simp [
    hInvξ,
    h3SpectralScalarRawFourier,
    Pi.smul_apply',
    smul_eq_mul
  ]

/-! ## Young bounds with quantitative H³ input -/

/--
Endpoint Young convolution with the first H³ input deweighted to Fourier
`L¹` and the second kept in weighted Fourier `L²`.
-/
noncomputable def h3SobolevYoungConvolution
    (F G : H3SpectralScalarState) :
    H3SpectralScalarState :=
  h3L1L2Convolution
    (h3SpectralScalarRawFourierHolderL1 F)
    G

/-- One-sided Young estimate with the Sobolev deweighting constant exposed. -/
theorem norm_h3SobolevYoungConvolution_le
    (F G : H3SpectralScalarState) :
    ‖h3SobolevYoungConvolution F G‖
      ≤
    h3SobolevDeweightingConstant * ‖F‖ * ‖G‖ := by
  calc
    ‖h3SobolevYoungConvolution F G‖
        ≤
      ‖h3SpectralScalarRawFourierHolderL1 F‖ * ‖G‖ := by
        exact
          norm_h3L1L2Convolution_le
            (h3SpectralScalarRawFourierHolderL1 F)
            G
    _ ≤
      (h3SobolevDeweightingConstant * ‖F‖) * ‖G‖ :=
        mul_le_mul_of_nonneg_right
          (norm_h3SpectralScalarRawFourierHolderL1_le F)
          (norm_nonneg G)
    _ =
      h3SobolevDeweightingConstant * ‖F‖ * ‖G‖ := by
        rfl

/-! ## Exact reweighting and the split convolution kernel -/

/-- Deweighting and reweighting are pointwise inverse operations. -/
theorem h3SpectralScalarRawFourier_reweight_pointwise
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    (h3SobolevFrequencyWeight ξ : ℂ) *
        h3SpectralScalarRawFourier G ξ
      =
    G ξ := by
  unfold
    h3SpectralScalarRawFourier
    h3SobolevFrequencyWeightInvComplex

  have hW :
      h3SobolevFrequencyWeight ξ ≠ 0 :=
    ne_of_gt (h3SobolevFrequencyWeight_pos ξ)

  have hReal :
      h3SobolevFrequencyWeight ξ *
          h3SobolevFrequencyWeightInv ξ
        =
      (1 : ℝ) := by
    unfold h3SobolevFrequencyWeightInv
    exact mul_inv_cancel₀ hW

  have hComplex :
      (h3SobolevFrequencyWeight ξ : ℂ) *
          (h3SobolevFrequencyWeightInv ξ : ℂ)
        =
      (1 : ℂ) := by
    exact_mod_cast hReal

  rw [← mul_assoc, hComplex, one_mul]

/--
Pointwise weighted-product kernel estimate obtained from the exact H³ weight
split.  This is the inequality that will be integrated in the Sobolev algebra
proof.
-/
theorem norm_h3WeightedRawProductKernel_le
    (F G : H3SpectralScalarState)
    (ξ η : H3FourierPoint3) :
    ‖(h3SobolevFrequencyWeight ξ : ℂ) *
        (h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η))‖
      ≤
    8 *
      (‖F η‖ *
          ‖h3SpectralScalarRawFourier G (ξ - η)‖
        +
       ‖h3SpectralScalarRawFourier F η‖ *
          ‖G (ξ - η)‖) := by
  have hF :
      ‖F η‖
        =
      h3SobolevFrequencyWeight η *
        ‖h3SpectralScalarRawFourier F η‖ := by
    rw [← h3SpectralScalarRawFourier_reweight_pointwise F η]
    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_pos (h3SobolevFrequencyWeight_pos η)
    ]

  have hG :
      ‖G (ξ - η)‖
        =
      h3SobolevFrequencyWeight (ξ - η) *
        ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
    rw [← h3SpectralScalarRawFourier_reweight_pointwise G (ξ - η)]
    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_pos (h3SobolevFrequencyWeight_pos (ξ - η))
    ]

  have hProdNonneg :
      0 ≤
        ‖h3SpectralScalarRawFourier F η‖ *
          ‖h3SpectralScalarRawFourier G (ξ - η)‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)

  calc
    ‖(h3SobolevFrequencyWeight ξ : ℂ) *
        (h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η))‖
        =
      h3SobolevFrequencyWeight ξ *
        (‖h3SpectralScalarRawFourier F η‖ *
          ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
          rw [
            norm_mul,
            Complex.norm_real,
            Real.norm_eq_abs,
            abs_of_pos (h3SobolevFrequencyWeight_pos ξ),
            norm_mul
          ]
    _ ≤
      (8 *
        (h3SobolevFrequencyWeight η
          + h3SobolevFrequencyWeight (ξ - η))) *
        (‖h3SpectralScalarRawFourier F η‖ *
          ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
            mul_le_mul_of_nonneg_right
              (h3SobolevFrequencyWeight_le_eight_mul_add ξ η)
              hProdNonneg
    _ =
      8 *
        ((h3SobolevFrequencyWeight η *
            ‖h3SpectralScalarRawFourier F η‖) *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖
          +
         ‖h3SpectralScalarRawFourier F η‖ *
            (h3SobolevFrequencyWeight (ξ - η) *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖)) := by
        ring
    _ =
      8 *
        (‖F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖
          +
         ‖h3SpectralScalarRawFourier F η‖ *
            ‖G (ξ - η)‖) := by
        rw [← hF, ← hG]

end

end Euclidean
end Bridge
end PrimeTensor
