import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.HeatTimeKernel

/-!
# Fin-indexed H³ vorticity flux bridge

The newer spectral product/heat-divergence closure was first packaged over
`Axis Depth.three`, because that is the native spatial index in the underlying
PrimeTensor differential layer.

The older mild restart/path-space API, however, is natively indexed by `Fin 3`.
Rather than inventing and maintaining an `Axis Depth.three ≃ Fin 3` inverse
only to erase it at the path boundary, this file exposes the same already-proved
scalar nonlinear estimates directly on the finite index used by the restart
layer.

No new analysis occurs here.  The scalar product estimate and the scalar
heat-derivative estimate are exactly the green results from
`WeightedConvolutionL2` and `HeatDivergence`.

The resulting finite-index nonlinear kernel satisfies

    ‖e^{νtΔ} div (U⊗Ω - Ω⊗U)‖
      ≤ 96 C_deweight (sqrt (ν t))⁻¹ ‖U‖ ‖Ω‖.

That is the form needed by the Duhamel/path-space rung.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- Restart-layer three-component H³ spectral vector state. -/
abbrev H3SpectralFinVectorState : Type :=
  Fin 3 → H3SpectralScalarState

/-- Restart-layer three-by-three H³ spectral tensor state. -/
abbrev H3SpectralFinTensorState : Type :=
  Fin 3 → Fin 3 → H3SpectralScalarState

/-- Every finite-index vector coordinate is controlled by the product sup norm. -/
theorem h3SpectralFinVector_coordinate_norm_le
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    ‖U i‖ ≤ ‖U‖ := by
  exact
    (pi_norm_le_iff_of_nonneg (norm_nonneg U)).1
      le_rfl i

/-- Every finite-index tensor coordinate is controlled by the iterated product sup norm. -/
theorem h3SpectralFinTensor_coordinate_norm_le
    (T : H3SpectralFinTensorState)
    (i j : Fin 3) :
    ‖T i j‖ ≤ ‖T‖ := by
  calc
    ‖T i j‖ ≤ ‖T i‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg (T i))).1
        le_rfl j
    _ ≤ ‖T‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg T)).1
        le_rfl i

/-- Fin-indexed weighted H³ spectral outer product. -/
noncomputable def h3SpectralFinOuterProduct
    (U V : H3SpectralFinVectorState) :
    H3SpectralFinTensorState :=
  fun i j =>
    h3WeightedRawProductConvolutionL2 (U i) (V j)

/-- Coordinatewise scalar H³ algebra estimate at the finite-index boundary. -/
theorem norm_h3SpectralFinOuterProduct_coordinate_le
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3) :
    ‖h3SpectralFinOuterProduct U V i j‖
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
    h3SpectralFinVector_coordinate_norm_le U i

  have hVj :
      ‖V j‖ ≤ ‖V‖ :=
    h3SpectralFinVector_coordinate_norm_le V j

  calc
    ‖h3SpectralFinOuterProduct U V i j‖
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

/-- Finite-dimensional lift of the scalar H³ algebra estimate. -/
theorem norm_h3SpectralFinOuterProduct_le
    (U V : H3SpectralFinVectorState) :
    ‖h3SpectralFinOuterProduct U V‖
      ≤
    16 * h3SobolevDeweightingConstant * ‖U‖ * ‖V‖ := by
  have hRhs :
      0 ≤ 16 * h3SobolevDeweightingConstant * ‖U‖ * ‖V‖ := by
    positivity [h3SobolevDeweightingConstant_nonneg]
  apply (pi_norm_le_iff_of_nonneg hRhs).2
  intro i
  apply (pi_norm_le_iff_of_nonneg hRhs).2
  intro j
  exact norm_h3SpectralFinOuterProduct_coordinate_le U V i j

/-- Fin-indexed antisymmetric vorticity flux. -/
noncomputable def h3SpectralFinVorticityFlux
    (U Ω : H3SpectralFinVectorState) :
    H3SpectralFinTensorState :=
  h3SpectralFinOuterProduct U Ω -
    h3SpectralFinOuterProduct Ω U

/-- Fin-indexed antisymmetric flux bound. -/
theorem norm_h3SpectralFinVorticityFlux_le
    (U Ω : H3SpectralFinVectorState) :
    ‖h3SpectralFinVorticityFlux U Ω‖
      ≤
    32 * h3SobolevDeweightingConstant * ‖U‖ * ‖Ω‖ := by
  calc
    ‖h3SpectralFinVorticityFlux U Ω‖
        ≤
      ‖h3SpectralFinOuterProduct U Ω‖ +
        ‖h3SpectralFinOuterProduct Ω U‖ := by
          simpa [h3SpectralFinVorticityFlux] using
            norm_sub_le
              (h3SpectralFinOuterProduct U Ω)
              (h3SpectralFinOuterProduct Ω U)
    _ ≤
      16 * h3SobolevDeweightingConstant * ‖U‖ * ‖Ω‖
        +
      16 * h3SobolevDeweightingConstant * ‖Ω‖ * ‖U‖ := by
          exact
            add_le_add
              (norm_h3SpectralFinOuterProduct_le U Ω)
              (norm_h3SpectralFinOuterProduct_le Ω U)
    _ =
      32 * h3SobolevDeweightingConstant * ‖U‖ * ‖Ω‖ := by
          ring

/--
Heat evolution after Fourier divergence of a finite-index spectral tensor.

The output coordinate `i` is

    Σⱼ e^{νtΔ} ∂ⱼ Tᵢⱼ.
-/
noncomputable def h3SpectralFinTensorHeatDivergenceApply
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (T : H3SpectralFinTensorState) :
    H3SpectralFinVectorState :=
  fun i =>
    ∑ j : Fin 3,
      h3SpectralScalarHeatDerivativeApply
        ν t hν ht j (T i j)

/-- Coordinate bound for the finite-index heat-smoothed divergence. -/
theorem norm_h3SpectralFinTensorHeatDivergenceApply_coordinate_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (T : H3SpectralFinTensorState)
    (i : Fin 3) :
    ‖h3SpectralFinTensorHeatDivergenceApply ν t hν ht T i‖
      ≤
    3 * (Real.sqrt (ν * t))⁻¹ * ‖T‖ := by
  have hc :
      0 ≤ (Real.sqrt (ν * t))⁻¹ := by
    positivity

  calc
    ‖h3SpectralFinTensorHeatDivergenceApply ν t hν ht T i‖
        ≤
      ∑ j : Fin 3,
        ‖h3SpectralScalarHeatDerivativeApply
          ν t hν ht j (T i j)‖ := by
          exact
            norm_sum_le
              Finset.univ
              (fun j : Fin 3 =>
                h3SpectralScalarHeatDerivativeApply
                  ν t hν ht j (T i j))
    _ ≤
      ∑ j : Fin 3,
        (Real.sqrt (ν * t))⁻¹ *
          ‖T i j‖ := by
          exact
            Finset.sum_le_sum
              (fun j _ =>
                norm_h3SpectralScalarHeatDerivativeApply_le
                  hν ht j (T i j))
    _ ≤
      ∑ _j : Fin 3,
        (Real.sqrt (ν * t))⁻¹ * ‖T‖ := by
          exact
            Finset.sum_le_sum
              (fun j _ =>
                mul_le_mul_of_nonneg_left
                  (h3SpectralFinTensor_coordinate_norm_le T i j)
                  hc)
    _ =
      3 * (Real.sqrt (ν * t))⁻¹ * ‖T‖ := by
          simp
          ring

/-- Full finite-index heat-divergence operator bound. -/
theorem norm_h3SpectralFinTensorHeatDivergenceApply_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (T : H3SpectralFinTensorState) :
    ‖h3SpectralFinTensorHeatDivergenceApply ν t hν ht T‖
      ≤
    3 * (Real.sqrt (ν * t))⁻¹ * ‖T‖ := by
  have hRhs :
      0 ≤ 3 * (Real.sqrt (ν * t))⁻¹ * ‖T‖ := by
    positivity
  apply (pi_norm_le_iff_of_nonneg hRhs).2
  intro i
  exact
    norm_h3SpectralFinTensorHeatDivergenceApply_coordinate_le
      hν ht T i

/-- Fin-indexed heat-smoothed vorticity nonlinear kernel. -/
noncomputable def h3SpectralFinVorticityHeatDivergenceApply
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (U Ω : H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  h3SpectralFinTensorHeatDivergenceApply
    ν t hν ht (h3SpectralFinVorticityFlux U Ω)

/--
Complete finite-index one-time nonlinear estimate, ready for the restart path
space.
-/
theorem norm_h3SpectralFinVorticityHeatDivergenceApply_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U Ω : H3SpectralFinVectorState) :
    ‖h3SpectralFinVorticityHeatDivergenceApply
        ν t hν ht U Ω‖
      ≤
    96 * h3SobolevDeweightingConstant *
      (Real.sqrt (ν * t))⁻¹ *
      ‖U‖ * ‖Ω‖ := by
  have hc :
      0 ≤ 3 * (Real.sqrt (ν * t))⁻¹ := by
    positivity

  calc
    ‖h3SpectralFinVorticityHeatDivergenceApply
        ν t hν ht U Ω‖
        ≤
      3 * (Real.sqrt (ν * t))⁻¹ *
        ‖h3SpectralFinVorticityFlux U Ω‖ :=
      norm_h3SpectralFinTensorHeatDivergenceApply_le
        hν ht (h3SpectralFinVorticityFlux U Ω)
    _ ≤
      3 * (Real.sqrt (ν * t))⁻¹ *
        (32 * h3SobolevDeweightingConstant * ‖U‖ * ‖Ω‖) :=
      mul_le_mul_of_nonneg_left
        (norm_h3SpectralFinVorticityFlux_le U Ω)
        hc
    _ =
      96 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ *
        ‖U‖ * ‖Ω‖ := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
