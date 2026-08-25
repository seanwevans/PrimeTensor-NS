import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralRawApproximation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.WeightedConvolutionBilinear

/-!
# Difference estimate for the weighted H³ product convolution

The genuine weighted product convolution is bilinear and satisfies the H³ algebra bound

    ‖B(F,G)‖ ≤ C ‖F‖ ‖G‖,

with `C = 16 * h3SobolevDeweightingConstant`.

This file packages the corresponding two-input difference estimate.  It is the quantitative
continuity statement needed to pass the Schwartz product/convolution identity through the
weighted spectral approximation constructed in `SchwartzSpectralRawApproximation`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3WeightedConvolutionDifference
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact polarization identity for the difference of two weighted convolutions. -/
theorem h3WeightedRawProductConvolutionL2_sub_eq
    (F F' G G' : H3SpectralScalarState) :
    h3WeightedRawProductConvolutionL2 F G -
        h3WeightedRawProductConvolutionL2 F' G'
      =
    h3WeightedRawProductConvolutionL2 (F - F') G +
        h3WeightedRawProductConvolutionL2 F' (G - G') := by
  rw [h3WeightedRawProductConvolutionL2_sub_left,
      h3WeightedRawProductConvolutionL2_sub_right]
  abel

/-- Joint difference estimate for the genuine weighted H³ product convolution. -/
theorem norm_h3WeightedRawProductConvolutionL2_sub_le
    (F F' G G' : H3SpectralScalarState) :
    ‖h3WeightedRawProductConvolutionL2 F G -
        h3WeightedRawProductConvolutionL2 F' G'‖
      ≤
    (16 * h3SobolevDeweightingConstant) * ‖F - F'‖ * ‖G‖ +
      (16 * h3SobolevDeweightingConstant) * ‖F'‖ * ‖G - G'‖ := by
  rw [h3WeightedRawProductConvolutionL2_sub_eq]
  exact
    (norm_add_le
      (h3WeightedRawProductConvolutionL2 (F - F') G)
      (h3WeightedRawProductConvolutionL2 F' (G - G'))).trans
      (add_le_add
        (norm_h3WeightedRawProductConvolutionL2_le (F - F') G)
        (norm_h3WeightedRawProductConvolutionL2_le F' (G - G')))

/-- One-sided Lipschitz estimate in the first input. -/
theorem norm_h3WeightedRawProductConvolutionL2_sub_left_le
    (F F' G : H3SpectralScalarState) :
    ‖h3WeightedRawProductConvolutionL2 F G -
        h3WeightedRawProductConvolutionL2 F' G‖
      ≤
    (16 * h3SobolevDeweightingConstant) * ‖F - F'‖ * ‖G‖ := by
  rw [← h3WeightedRawProductConvolutionL2_sub_left]
  exact norm_h3WeightedRawProductConvolutionL2_le (F - F') G

/-- One-sided Lipschitz estimate in the second input. -/
theorem norm_h3WeightedRawProductConvolutionL2_sub_right_le
    (F G G' : H3SpectralScalarState) :
    ‖h3WeightedRawProductConvolutionL2 F G -
        h3WeightedRawProductConvolutionL2 F G'‖
      ≤
    (16 * h3SobolevDeweightingConstant) * ‖F‖ * ‖G - G'‖ := by
  rw [← h3WeightedRawProductConvolutionL2_sub_right]
  exact norm_h3WeightedRawProductConvolutionL2_le F (G - G')

end

end Euclidean
end Bridge
end PrimeTensor
