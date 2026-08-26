import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Vorticity.Flux
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Heat.Smoothing

/-!
# Heat-smoothed divergence of the H³ vorticity flux

The quadratic vorticity flux is now an honest H³ spectral tensor.  The mild
equation applies one divergence derivative after that product and then the heat
semigroup.  This is exactly where the derivative is affordable.

For one coordinate derivative Mathlib's Fourier convention gives the symbol

    2π i ξⱼ.

`HeatSmoothing` already proves the radial envelope

    ‖(2π |ξ|) exp (-ν t (2π |ξ|)²)‖
      ≤ (sqrt (ν t))⁻¹.

Every coordinate symbol is bounded by the radial magnitude, so the same
estimate holds coordinatewise.  Summing the three divergence directions costs
only the finite-dimensional factor `3`.

Applied to the antisymmetric flux this yields

    ‖e^{νtΔ} div (U⊗Ω - Ω⊗U)‖_{H³}
      ≤ 96 C_deweight (sqrt (ν t))⁻¹ ‖U‖_{H³} ‖Ω‖_{H³}.

This is the singular kernel needed for the next Duhamel/path-space rung.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3HeatDivergence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Coordinate derivative under heat evolution -/

/--
One coordinate derivative followed by heat evolution, as a Fourier multiplier.
-/
def h3HeatDerivativeSymbol
    (ν t : ℝ)
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol j ξ *
    h3HeatFourierSymbol ν t ξ

/-- Each coordinate derivative symbol is bounded by the radial gradient magnitude. -/
theorem norm_h3FourierDerivativeSymbol_le_gradientMagnitude
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3FourierDerivativeSymbol j ξ‖
      ≤ h3FourierGradientMagnitude ξ := by
  have hsingle :
      ‖h3FourierDerivativeSymbol j ξ‖ ^ 2
        ≤
      ∑ i : Fin 3,
        ‖h3FourierDerivativeSymbol i ξ‖ ^ 2 := by
    exact
      Finset.single_le_sum
        (fun i _ => sq_nonneg ‖h3FourierDerivativeSymbol i ξ‖)
        (Finset.mem_univ j)

  have hsq :
      ‖h3FourierDerivativeSymbol j ξ‖ ^ 2
        ≤
      (h3FourierGradientMagnitude ξ) ^ 2 := by
    calc
      ‖h3FourierDerivativeSymbol j ξ‖ ^ 2
          ≤
        ∑ i : Fin 3,
          ‖h3FourierDerivativeSymbol i ξ‖ ^ 2 :=
        hsingle
      _ = h3FourierGradientSquare ξ :=
        sum_norm_h3FourierDerivativeSymbol_sq ξ
      _ = (h3FourierGradientMagnitude ξ) ^ 2 :=
        (h3FourierGradientMagnitude_sq ξ).symm

  nlinarith [
    norm_nonneg (h3FourierDerivativeSymbol j ξ),
    h3FourierGradientMagnitude_nonneg ξ
  ]

/-- The directional heat-derivative multiplier is continuous in frequency. -/
theorem continuous_h3HeatDerivativeSymbol
    (ν t : ℝ)
    (j : Fin 3) :
    Continuous (h3HeatDerivativeSymbol ν t j) := by
  unfold h3HeatDerivativeSymbol
  exact
    (h3FourierDerivativeSymbol_continuous j).mul
      (continuous_h3HeatFourierSymbol ν t)

/-- Coordinatewise one-derivative heat smoothing with the radial sharp envelope. -/
theorem norm_h3HeatDerivativeSymbol_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3HeatDerivativeSymbol ν t j ξ‖
      ≤
    (Real.sqrt (ν * t))⁻¹ := by
  have hrad :
      ‖h3HeatGradientMagnitudeSymbol ν t ξ‖
        =
      h3FourierGradientMagnitude ξ *
        ‖h3HeatFourierSymbol ν t ξ‖ := by
    rw [h3HeatGradientMagnitudeSymbol, norm_mul, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_nonneg (h3FourierGradientMagnitude_nonneg ξ)]

  calc
    ‖h3HeatDerivativeSymbol ν t j ξ‖
        =
      ‖h3FourierDerivativeSymbol j ξ‖ *
        ‖h3HeatFourierSymbol ν t ξ‖ := by
          rw [h3HeatDerivativeSymbol, norm_mul]
    _ ≤
      h3FourierGradientMagnitude ξ *
        ‖h3HeatFourierSymbol ν t ξ‖ :=
      mul_le_mul_of_nonneg_right
        (norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ)
        (norm_nonneg _)
    _ =
      ‖h3HeatGradientMagnitudeSymbol ν t ξ‖ :=
      hrad.symm
    _ ≤
      (Real.sqrt (ν * t))⁻¹ :=
      norm_h3HeatGradientMagnitudeSymbol_le hν ht ξ

/-- The coordinate heat-derivative multiplier preserves the weighted spectral `L²` state. -/
theorem h3HeatDerivativeFrequency_memLp
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3HeatDerivativeSymbol ν t j ξ * G ξ)
      2 volume := by
  refine
    (MeasureTheory.Lp.memLp G).of_le_mul
      (c := (Real.sqrt (ν * t))⁻¹)
      ?_ ?_
  · exact
      (continuous_h3HeatDerivativeSymbol ν t j).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable G)
  · filter_upwards with ξ
    calc
      ‖h3HeatDerivativeSymbol ν t j ξ * G ξ‖
          =
        ‖h3HeatDerivativeSymbol ν t j ξ‖ * ‖G ξ‖ := by
          rw [norm_mul]
      _ ≤
        (Real.sqrt (ν * t))⁻¹ * ‖G ξ‖ :=
      mul_le_mul_of_nonneg_right
        (norm_h3HeatDerivativeSymbol_le hν ht j ξ)
        (norm_nonneg _)

/-- Apply one coordinate derivative and then heat evolution to one H³ spectral scalar state. -/
noncomputable def h3SpectralScalarHeatDerivativeApply
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    H3SpectralScalarState :=
  (h3HeatDerivativeFrequency_memLp hν ht j G).toLp
    (fun ξ : H3FourierPoint3 =>
      h3HeatDerivativeSymbol ν t j ξ * G ξ)

/-- Pointwise representative of the coordinate heat-derivative operator. -/
theorem h3SpectralScalarHeatDerivativeApply_ae
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    (h3SpectralScalarHeatDerivativeApply
        ν t hν ht j G :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      h3HeatDerivativeSymbol ν t j ξ * G ξ) := by
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3HeatDerivativeFrequency_memLp hν ht j G)

/-- Coordinatewise one-gradient heat smoothing on one weighted H³ component. -/
theorem norm_h3SpectralScalarHeatDerivativeApply_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarHeatDerivativeApply ν t hν ht j G‖
      ≤
    (Real.sqrt (ν * t))⁻¹ * ‖G‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    h3SpectralScalarHeatDerivativeApply_ae hν ht j G
  ] with ξ hξ
  rw [hξ, norm_mul]
  exact
    mul_le_mul_of_nonneg_right
      (norm_h3HeatDerivativeSymbol_le hν ht j ξ)
      (norm_nonneg _)

/-! ## Tensor divergence -/

/--
Heat evolution after the Fourier divergence of a three-by-three H³ tensor.

The output coordinate `i` is

    Σⱼ e^{νtΔ} ∂ⱼ Tᵢⱼ.
-/
noncomputable def h3SpectralTensorHeatDivergenceApply
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (T : H3SpectralTensorState) :
    H3SpectralVectorState :=
  fun i =>
    ∑ j : Fin 3,
      h3SpectralScalarHeatDerivativeApply
        ν t hν ht j (T i (h3AxisOfFin3 j))

/-- Coordinate bound for the heat-smoothed tensor divergence. -/
theorem norm_h3SpectralTensorHeatDivergenceApply_coordinate_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (T : H3SpectralTensorState)
    (i : PrimeTensor.Axis Depth.three) :
    ‖h3SpectralTensorHeatDivergenceApply ν t hν ht T i‖
      ≤
    3 * (Real.sqrt (ν * t))⁻¹ * ‖T‖ := by
  have hc :
      0 ≤ (Real.sqrt (ν * t))⁻¹ := by
    positivity

  calc
    ‖h3SpectralTensorHeatDivergenceApply ν t hν ht T i‖
        ≤
      ∑ j : Fin 3,
        ‖h3SpectralScalarHeatDerivativeApply
          ν t hν ht j (T i (h3AxisOfFin3 j))‖ := by
          exact
            norm_sum_le
              Finset.univ
              (fun j : Fin 3 =>
                h3SpectralScalarHeatDerivativeApply
                  ν t hν ht j (T i (h3AxisOfFin3 j)))
    _ ≤
      ∑ j : Fin 3,
        (Real.sqrt (ν * t))⁻¹ *
          ‖T i (h3AxisOfFin3 j)‖ := by
          exact
            Finset.sum_le_sum
              (fun j _ =>
                norm_h3SpectralScalarHeatDerivativeApply_le
                  hν ht j (T i (h3AxisOfFin3 j)))
    _ ≤
      ∑ _j : Fin 3,
        (Real.sqrt (ν * t))⁻¹ * ‖T‖ := by
          exact
            Finset.sum_le_sum
              (fun j _ =>
                mul_le_mul_of_nonneg_left
                  (h3SpectralTensor_coordinate_norm_le
                    T i (h3AxisOfFin3 j))
                  hc)
    _ =
      3 * (Real.sqrt (ν * t))⁻¹ * ‖T‖ := by
          simp
          ring

/-- Full finite-dimensional heat-divergence operator bound. -/
theorem norm_h3SpectralTensorHeatDivergenceApply_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (T : H3SpectralTensorState) :
    ‖h3SpectralTensorHeatDivergenceApply ν t hν ht T‖
      ≤
    3 * (Real.sqrt (ν * t))⁻¹ * ‖T‖ := by
  have hRhs :
      0 ≤ 3 * (Real.sqrt (ν * t))⁻¹ * ‖T‖ := by
    positivity
  apply (pi_norm_le_iff_of_nonneg hRhs).2
  intro i
  exact
    norm_h3SpectralTensorHeatDivergenceApply_coordinate_le
      hν ht T i

/-! ## Vorticity flux specialization -/

/--
Heat-smoothed divergence of the antisymmetric H³ vorticity flux.
-/
noncomputable def h3SpectralVorticityHeatDivergenceApply
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (U Ω : H3SpectralVectorState) :
    H3SpectralVectorState :=
  h3SpectralTensorHeatDivergenceApply
    ν t hν ht (h3SpectralVorticityFlux U Ω)

/--
The complete one-time vorticity nonlinear kernel estimate.

The quadratic flux contributes `32 C_deweight`; the three-coordinate
divergence contributes `3`; heat pays the derivative with
`(sqrt (ν t))⁻¹`.
-/
theorem norm_h3SpectralVorticityHeatDivergenceApply_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U Ω : H3SpectralVectorState) :
    ‖h3SpectralVorticityHeatDivergenceApply
        ν t hν ht U Ω‖
      ≤
    96 * h3SobolevDeweightingConstant *
      (Real.sqrt (ν * t))⁻¹ *
      ‖U‖ * ‖Ω‖ := by
  have hc :
      0 ≤ 3 * (Real.sqrt (ν * t))⁻¹ := by
    positivity

  calc
    ‖h3SpectralVorticityHeatDivergenceApply
        ν t hν ht U Ω‖
        ≤
      3 * (Real.sqrt (ν * t))⁻¹ *
        ‖h3SpectralVorticityFlux U Ω‖ :=
      norm_h3SpectralTensorHeatDivergenceApply_le
        hν ht (h3SpectralVorticityFlux U Ω)
    _ ≤
      3 * (Real.sqrt (ν * t))⁻¹ *
        (32 * h3SobolevDeweightingConstant * ‖U‖ * ‖Ω‖) :=
      mul_le_mul_of_nonneg_left
        (norm_h3SpectralVorticityFlux_le U Ω)
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
