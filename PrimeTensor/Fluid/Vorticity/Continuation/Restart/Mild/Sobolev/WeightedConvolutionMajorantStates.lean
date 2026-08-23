import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.YoungConvolutionReal

/-!
# Real L¹/L² states underlying the weighted H³ Young majorants

The scalar majorants use only norms:

    A(F,G)(ξ) = ∫ η, ‖ĝ(η)‖ ‖F(ξ - η)‖,
    B(F,G)(ξ) = ∫ η, ‖f̂(η)‖ ‖G(ξ - η)‖.

This file packages the two kinds of factors as genuine real `L¹` and `L²`
states.  The raw norm is taken from the already constructed Hölder `L¹`
state, while the weighted norm is taken directly from the spectral `L²`
state.  Since `eLpNorm` is unchanged by taking pointwise norms, these real
states inherit the exact bundled norms.

We then feed them to the real endpoint Young construction.  The resulting
`L²` states are *candidates* for the named scalar majorants; the next bridge
will identify their representatives almost everywhere without using point
evaluation on `L²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3WeightedConvolutionMajorantStates
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real `L¹` state represented by the norm of the raw Fourier amplitude. -/
noncomputable def h3RawFourierNormRealL1
    (G : H3SpectralScalarState) :
    H3FourierRealL1 :=
  ((MeasureTheory.Lp.memLp
      (h3SpectralScalarRawFourierHolderL1 G)).norm).toLp
    (fun ξ : H3FourierPoint3 =>
      ‖h3SpectralScalarRawFourierHolderL1 G ξ‖)

/-- The real raw-norm `L¹` state represents `ξ ↦ ‖ĝ ξ‖` a.e. -/
theorem h3RawFourierNormRealL1_ae
    (G : H3SpectralScalarState) :
    (h3RawFourierNormRealL1 G : H3FourierPoint3 → ℝ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      ‖h3SpectralScalarRawFourier G ξ‖) := by
  have hToLp :=
    MemLp.coeFn_toLp
      ((MeasureTheory.Lp.memLp
        (h3SpectralScalarRawFourierHolderL1 G)).norm)
  have hRaw := h3SpectralScalarRawFourierHolderL1_ae G
  filter_upwards [hToLp, hRaw] with ξ hToLpξ hRawξ
  exact hToLpξ.trans (congrArg norm hRawξ)

/-- Taking the pointwise norm does not change the bundled `L¹` norm. -/
theorem norm_h3RawFourierNormRealL1
    (G : H3SpectralScalarState) :
    ‖h3RawFourierNormRealL1 G‖
      = ‖h3SpectralScalarRawFourierHolderL1 G‖ := by
  calc
    ‖h3RawFourierNormRealL1 G‖
        =
      ENNReal.toReal
        (eLpNorm
          (fun ξ : H3FourierPoint3 =>
            ‖h3SpectralScalarRawFourierHolderL1 G ξ‖)
          1
          (volume : Measure H3FourierPoint3)) := by
            rw [h3RawFourierNormRealL1, MeasureTheory.Lp.norm_toLp]
    _ =
      ENNReal.toReal
        (eLpNorm
          (h3SpectralScalarRawFourierHolderL1 G :
            H3FourierPoint3 → ℂ)
          1
          (volume : Measure H3FourierPoint3)) := by
            rw [eLpNorm_norm]
    _ = ‖h3SpectralScalarRawFourierHolderL1 G‖ :=
      (MeasureTheory.Lp.norm_def _).symm

/-- Quantitative real `L¹` raw-norm bound inherited from H³ deweighting. -/
theorem norm_h3RawFourierNormRealL1_le
    (G : H3SpectralScalarState) :
    ‖h3RawFourierNormRealL1 G‖
      ≤ h3SobolevDeweightingConstant * ‖G‖ := by
  rw [norm_h3RawFourierNormRealL1]
  exact norm_h3SpectralScalarRawFourierHolderL1_le G

/-- Real `L²` state represented by the pointwise norm of a weighted spectral state. -/
noncomputable def h3WeightedNormRealL2
    (F : H3SpectralScalarState) :
    H3FourierRealL2 :=
  ((MeasureTheory.Lp.memLp F).norm).toLp
    (fun ξ : H3FourierPoint3 => ‖F ξ‖)

/-- The weighted-norm real state has the expected representative a.e. -/
theorem h3WeightedNormRealL2_ae
    (F : H3SpectralScalarState) :
    (h3WeightedNormRealL2 F : H3FourierPoint3 → ℝ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 => ‖F ξ‖) := by
  exact
    MemLp.coeFn_toLp
      ((MeasureTheory.Lp.memLp F).norm)

/-- Taking pointwise norm does not change the bundled weighted `L²` norm. -/
theorem norm_h3WeightedNormRealL2
    (F : H3SpectralScalarState) :
    ‖h3WeightedNormRealL2 F‖ = ‖F‖ := by
  calc
    ‖h3WeightedNormRealL2 F‖
        =
      ENNReal.toReal
        (eLpNorm
          (fun ξ : H3FourierPoint3 => ‖F ξ‖)
          2
          (volume : Measure H3FourierPoint3)) := by
            rw [h3WeightedNormRealL2, MeasureTheory.Lp.norm_toLp]
    _ =
      ENNReal.toReal
        (eLpNorm
          (F : H3FourierPoint3 → ℂ)
          2
          (volume : Measure H3FourierPoint3)) := by
            rw [eLpNorm_norm]
    _ = ‖F‖ :=
      (MeasureTheory.Lp.norm_def _).symm

/-- Abstract real-Young `L²` candidate for the first named majorant. -/
noncomputable def h3FirstYoungMajorantCandidateL2
    (F G : H3SpectralScalarState) :
    H3FourierRealL2 :=
  h3RealL1L2Convolution
    (h3RawFourierNormRealL1 G)
    (h3WeightedNormRealL2 F)

/-- Abstract real-Young `L²` candidate for the second named majorant. -/
noncomputable def h3SecondYoungMajorantCandidateL2
    (F G : H3SpectralScalarState) :
    H3FourierRealL2 :=
  h3RealL1L2Convolution
    (h3RawFourierNormRealL1 F)
    (h3WeightedNormRealL2 G)

/-- Endpoint Young bound for the first abstract majorant candidate. -/
theorem norm_h3FirstYoungMajorantCandidateL2_le
    (F G : H3SpectralScalarState) :
    ‖h3FirstYoungMajorantCandidateL2 F G‖
      ≤ h3SobolevDeweightingConstant * ‖G‖ * ‖F‖ := by
  calc
    ‖h3FirstYoungMajorantCandidateL2 F G‖
        ≤
      ‖h3RawFourierNormRealL1 G‖ *
        ‖h3WeightedNormRealL2 F‖ :=
      norm_h3RealL1L2Convolution_le _ _
    _ = ‖h3RawFourierNormRealL1 G‖ * ‖F‖ := by
      rw [norm_h3WeightedNormRealL2]
    _ ≤
      (h3SobolevDeweightingConstant * ‖G‖) * ‖F‖ :=
      mul_le_mul_of_nonneg_right
        (norm_h3RawFourierNormRealL1_le G)
        (norm_nonneg F)
    _ = h3SobolevDeweightingConstant * ‖G‖ * ‖F‖ := by
      rfl

/-- Endpoint Young bound for the second abstract majorant candidate. -/
theorem norm_h3SecondYoungMajorantCandidateL2_le
    (F G : H3SpectralScalarState) :
    ‖h3SecondYoungMajorantCandidateL2 F G‖
      ≤ h3SobolevDeweightingConstant * ‖F‖ * ‖G‖ := by
  calc
    ‖h3SecondYoungMajorantCandidateL2 F G‖
        ≤
      ‖h3RawFourierNormRealL1 F‖ *
        ‖h3WeightedNormRealL2 G‖ :=
      norm_h3RealL1L2Convolution_le _ _
    _ = ‖h3RawFourierNormRealL1 F‖ * ‖G‖ := by
      rw [norm_h3WeightedNormRealL2]
    _ ≤
      (h3SobolevDeweightingConstant * ‖F‖) * ‖G‖ :=
      mul_le_mul_of_nonneg_right
        (norm_h3RawFourierNormRealL1_le F)
        (norm_nonneg G)
    _ = h3SobolevDeweightingConstant * ‖F‖ * ‖G‖ := by
      rfl

end

end Euclidean
end Bridge
end PrimeTensor
