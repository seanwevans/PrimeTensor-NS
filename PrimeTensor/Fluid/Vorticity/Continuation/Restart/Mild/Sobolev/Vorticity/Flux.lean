import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weighted.Convolution.L2

/-!
# Three-dimensional H³ spectral product tensors and vorticity flux

The scalar weighted Fourier convolution is now known to satisfy the genuine
H³ algebra estimate

    ‖F ⋆₃ G‖₂ ≤ 16 C_deweight ‖F‖₂ ‖G‖₂.

The mild Navier--Stokes/vorticity nonlinearity should not spend a derivative
before this product estimate is used.  In divergence form the quadratic
objects are tensor products, with the derivative applied afterwards and paid
for by the heat kernel.

This file therefore performs only the finite-dimensional lift:

    (U ⊗ V)ᵢⱼ = Uᵢ Vⱼ,

where each scalar product is the already constructed genuine weighted Fourier
convolution.  It then packages the antisymmetric vorticity flux

    U ⊗ Ω - Ω ⊗ U.

No derivative or heat estimate is used here.  Those belong to the next rung.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3VorticityFlux
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Three-component H³ spectral vector state. -/
abbrev H3SpectralVectorState : Type :=
  PrimeTensor.Axis Depth.three → H3SpectralScalarState

/-- Three-by-three H³ spectral tensor state. -/
abbrev H3SpectralTensorState : Type :=
  PrimeTensor.Axis Depth.three →
    PrimeTensor.Axis Depth.three →
      H3SpectralScalarState

/-- Every vector coordinate is controlled by the finite-product sup norm. -/
theorem h3SpectralVector_coordinate_norm_le
    (U : H3SpectralVectorState)
    (i : PrimeTensor.Axis Depth.three) :
    ‖U i‖ ≤ ‖U‖ := by
  exact
    (pi_norm_le_iff_of_nonneg (norm_nonneg U)).1
      le_rfl i

/-- Every tensor coordinate is controlled by the iterated finite-product sup norm. -/
theorem h3SpectralTensor_coordinate_norm_le
    (T : H3SpectralTensorState)
    (i j : PrimeTensor.Axis Depth.three) :
    ‖T i j‖ ≤ ‖T‖ := by
  calc
    ‖T i j‖ ≤ ‖T i‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg (T i))).1
        le_rfl j
    _ ≤ ‖T‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg T)).1
        le_rfl i

/--
Weighted H³ spectral outer product.

Each scalar entry is the genuine weighted Fourier convolution already closed
in `WeightedConvolutionL2`.
-/
noncomputable def h3SpectralOuterProduct
    (U V : H3SpectralVectorState) :
    H3SpectralTensorState :=
  fun i j =>
    h3WeightedRawProductConvolutionL2 (U i) (V j)

/-- Coordinatewise H³ algebra estimate for the spectral outer product. -/
theorem norm_h3SpectralOuterProduct_coordinate_le
    (U V : H3SpectralVectorState)
    (i j : PrimeTensor.Axis Depth.three) :
    ‖h3SpectralOuterProduct U V i j‖
      ≤
    16 * h3SobolevDeweightingConstant * ‖U‖ * ‖V‖ := by
  have hK :
      0 ≤ 16 * h3SobolevDeweightingConstant := by
    exact
      mul_nonneg
        (by norm_num)
        h3SobolevDeweightingConstant_nonneg

  have hUi :
      ‖U i‖ ≤ ‖U‖ :=
    h3SpectralVector_coordinate_norm_le U i

  have hVj :
      ‖V j‖ ≤ ‖V‖ :=
    h3SpectralVector_coordinate_norm_le V j

  calc
    ‖h3SpectralOuterProduct U V i j‖
        ≤
      16 * h3SobolevDeweightingConstant * ‖U i‖ * ‖V j‖ :=
      norm_h3WeightedRawProductConvolutionL2_le (U i) (V j)
    _ ≤
      16 * h3SobolevDeweightingConstant * ‖U‖ * ‖V j‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hUi hK)
            (norm_nonneg (V j))
    _ ≤
      16 * h3SobolevDeweightingConstant * ‖U‖ * ‖V‖ := by
        exact
          mul_le_mul_of_nonneg_left
            hVj
            (mul_nonneg hK (norm_nonneg U))

/-- Finite-dimensional lift of the scalar H³ algebra estimate to `3 × 3` tensors. -/
theorem norm_h3SpectralOuterProduct_le
    (U V : H3SpectralVectorState) :
    ‖h3SpectralOuterProduct U V‖
      ≤
    16 * h3SobolevDeweightingConstant * ‖U‖ * ‖V‖ := by
  apply
    (pi_norm_le_iff_of_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) h3SobolevDeweightingConstant_nonneg)
          (norm_nonneg U))
        (norm_nonneg V))).2
  intro i
  apply
    (pi_norm_le_iff_of_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) h3SobolevDeweightingConstant_nonneg)
          (norm_nonneg U))
        (norm_nonneg V))).2
  intro j
  exact norm_h3SpectralOuterProduct_coordinate_le U V i j

/--
Antisymmetric quadratic flux underlying the divergence-form vorticity
nonlinearity.

Depending on sign convention the PDE uses this tensor or its negative; the
norm estimate is identical.
-/
noncomputable def h3SpectralVorticityFlux
    (U Ω : H3SpectralVectorState) :
    H3SpectralTensorState :=
  h3SpectralOuterProduct U Ω -
    h3SpectralOuterProduct Ω U

/-- The antisymmetric vorticity flux costs at most twice the scalar product constant. -/
theorem norm_h3SpectralVorticityFlux_le
    (U Ω : H3SpectralVectorState) :
    ‖h3SpectralVorticityFlux U Ω‖
      ≤
    32 * h3SobolevDeweightingConstant * ‖U‖ * ‖Ω‖ := by
  calc
    ‖h3SpectralVorticityFlux U Ω‖
        ≤
      ‖h3SpectralOuterProduct U Ω‖ +
        ‖h3SpectralOuterProduct Ω U‖ := by
          simpa [h3SpectralVorticityFlux] using
            norm_sub_le
              (h3SpectralOuterProduct U Ω)
              (h3SpectralOuterProduct Ω U)
    _ ≤
      16 * h3SobolevDeweightingConstant * ‖U‖ * ‖Ω‖
        +
      16 * h3SobolevDeweightingConstant * ‖Ω‖ * ‖U‖ := by
          exact
            add_le_add
              (norm_h3SpectralOuterProduct_le U Ω)
              (norm_h3SpectralOuterProduct_le Ω U)
    _ =
      32 * h3SobolevDeweightingConstant * ‖U‖ * ‖Ω‖ := by
          ring

end

end Euclidean
end Bridge
end PrimeTensor
