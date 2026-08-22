import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SobolevAlgebra
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.YoungConvolutionPairing

/-!
# Raw Fourier H³ states as L² functions

A weighted spectral scalar state `G` represents `W₃ * ĝ`.  The raw Fourier
amplitude is therefore `W₃⁻¹ * G`.

`SpectralL1` already proves that this raw amplitude is in `L¹`, which is the
input needed for the endpoint Young convolution.  For the direct weighted
Bochner construction we also need the simpler fact that it remains in `L²`.
Since the exact H³ weight satisfies `1 ≤ W₃`, its reciprocal is pointwise at
most one, hence deweighting is an `L²` contraction.

This file packages that fact without yet constructing the weighted product.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3RawFourierL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact inverse H³ weight is pointwise bounded above by one. -/
theorem h3SobolevFrequencyWeightInv_le_one
    (ξ : H3FourierPoint3) :
    h3SobolevFrequencyWeightInv ξ ≤ 1 := by
  unfold h3SobolevFrequencyWeightInv
  exact inv_le_one_of_one_le₀ (one_le_h3SobolevFrequencyWeight ξ)

/-- Deweighting a spectral H³ scalar state preserves `L²`. -/
theorem h3SpectralScalarRawFourier_memLp2
    (G : H3SpectralScalarState) :
    MemLp
      (h3SpectralScalarRawFourier G)
      2
      (volume : Measure H3FourierPoint3) := by
  apply
    (MeasureTheory.Lp.memLp G).of_le
      (h3SpectralScalarRawFourier_memLp1 G).1

  filter_upwards with ξ

  have hInvNonneg :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact inv_nonneg.mpr
      (h3SobolevFrequencyWeight_pos ξ).le

  have hInvLe :
      h3SobolevFrequencyWeightInv ξ ≤ 1 :=
    h3SobolevFrequencyWeightInv_le_one ξ

  calc
    ‖h3SpectralScalarRawFourier G ξ‖
        =
      h3SobolevFrequencyWeightInv ξ * ‖G ξ‖ := by
        rw [
          h3SpectralScalarRawFourier,
          h3SobolevFrequencyWeightInvComplex,
          norm_mul,
          Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_nonneg hInvNonneg
        ]
    _ ≤ 1 * ‖G ξ‖ :=
      mul_le_mul_of_nonneg_right hInvLe (norm_nonneg _)
    _ = ‖G ξ‖ := by
      rw [one_mul]

/-- Canonical `L²` package of the raw Fourier amplitude. -/
noncomputable def h3SpectralScalarRawFourierL2
    (G : H3SpectralScalarState) :
    H3FourierComplexL2 :=
  (h3SpectralScalarRawFourier_memLp2 G).toLp
    (h3SpectralScalarRawFourier G)

/-- The packaged raw `L²` state has the expected representative a.e. -/
theorem h3SpectralScalarRawFourierL2_ae
    (G : H3SpectralScalarState) :
    (h3SpectralScalarRawFourierL2 G :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    h3SpectralScalarRawFourier G := by
  exact
    MemLp.coeFn_toLp
      (h3SpectralScalarRawFourier_memLp2 G)

/-- Deweighting is contractive on Fourier `L²`. -/
theorem norm_h3SpectralScalarRawFourierL2_le
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarRawFourierL2 G‖ ≤ ‖G‖ := by
  rw [
    h3SpectralScalarRawFourierL2,
    MeasureTheory.Lp.norm_toLp,
    MeasureTheory.Lp.norm_def
  ]

  refine ENNReal.toReal_mono (MeasureTheory.Lp.eLpNorm_ne_top G) ?_

  apply eLpNorm_mono_ae
  filter_upwards with ξ

  have hInvNonneg :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact inv_nonneg.mpr
      (h3SobolevFrequencyWeight_pos ξ).le

  have hInvLe :
      h3SobolevFrequencyWeightInv ξ ≤ 1 :=
    h3SobolevFrequencyWeightInv_le_one ξ

  calc
    ‖h3SpectralScalarRawFourier G ξ‖
        =
      h3SobolevFrequencyWeightInv ξ * ‖G ξ‖ := by
        rw [
          h3SpectralScalarRawFourier,
          h3SobolevFrequencyWeightInvComplex,
          norm_mul,
          Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_nonneg hInvNonneg
        ]
    _ ≤ 1 * ‖G ξ‖ :=
      mul_le_mul_of_nonneg_right hInvLe (norm_nonneg _)
    _ = ‖G ξ‖ := by
      rw [one_mul]

end

end Euclidean
end Bridge
end PrimeTensor
