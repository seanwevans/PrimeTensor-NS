import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Encoder
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq

/-!
# One-gradient heat smoothing in the weighted H³ spectral state

The mild Navier--Stokes bilinear term needs the singular semigroup estimate

    ‖∇ exp(ν t Δ) G‖₂
      ≤ (sqrt (ν t))⁻¹ ‖G‖₂,

for positive viscosity and positive elapsed time.

Because `H3SpectralScalarState` already stores the weighted Fourier amplitude
`W₃ f̂`, the Sobolev weight commutes with both the scalar heat multiplier and
the radial gradient multiplier.  Thus the estimate is an ordinary bounded
multiplier estimate on complex `L²`.

For Mathlib's Fourier convention, the radial gradient magnitude is

    x(ξ) = 2π ‖ξ‖,

and the heat factor is

    exp (-(ν t) x(ξ)²).

Mathlib already proves the sharp-enough elementary estimate

    |x exp (-ε x²)| ≤ (sqrt ε)⁻¹

for `ε > 0` as `Real.abs_mulExpNegMulSq_le`.

This file packages that pointwise fact as an `L²` operator on the scalar and
three-component weighted spectral H³ solver states.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3HeatSmoothing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Radial Fourier gradient multiplier -/

/-- Radial Fourier gradient magnitude `2π ‖ξ‖`. -/
def h3FourierGradientMagnitude
    (ξ : H3FourierPoint3) : ℝ :=
  (2 * Real.pi) * ‖ξ‖

/-- The radial Fourier gradient magnitude is nonnegative. -/
theorem h3FourierGradientMagnitude_nonneg
    (ξ : H3FourierPoint3) :
    0 ≤ h3FourierGradientMagnitude ξ := by
  unfold h3FourierGradientMagnitude
  positivity

/--
The square of the radial gradient magnitude is exactly the existing
square-gradient factor `q(ξ)`.
-/
theorem h3FourierGradientMagnitude_sq
    (ξ : H3FourierPoint3) :
    (h3FourierGradientMagnitude ξ) ^ 2
      =
    h3FourierGradientSquare ξ := by
  unfold h3FourierGradientMagnitude h3FourierGradientSquare
  ring

/--
Complex Fourier multiplier for one radial gradient followed by heat evolution.
-/
def h3HeatGradientMagnitudeSymbol
    (ν t : ℝ)
    (ξ : H3FourierPoint3) : ℂ :=
  (h3FourierGradientMagnitude ξ : ℂ) *
    h3HeatFourierSymbol ν t ξ

/-- The heat-gradient multiplier is continuous in frequency. -/
theorem continuous_h3HeatGradientMagnitudeSymbol
    (ν t : ℝ) :
    Continuous (h3HeatGradientMagnitudeSymbol ν t) := by
  unfold h3HeatGradientMagnitudeSymbol
  apply Continuous.mul
  · exact
      Complex.continuous_ofReal.comp
        (by
          unfold h3FourierGradientMagnitude
          fun_prop)
  · exact continuous_h3HeatFourierSymbol ν t

/--
The heat-gradient multiplier is exactly the scalar function
`x exp (-(ν t) x²)` in norm, with `x = 2π ‖ξ‖`.
-/
theorem norm_h3HeatGradientMagnitudeSymbol_eq
    (ν t : ℝ)
    (ξ : H3FourierPoint3) :
    ‖h3HeatGradientMagnitudeSymbol ν t ξ‖
      =
    Real.mulExpNegMulSq
      (ν * t)
      (h3FourierGradientMagnitude ξ) := by
  have hx :
      0 ≤ h3FourierGradientMagnitude ξ :=
    h3FourierGradientMagnitude_nonneg ξ

  unfold h3HeatGradientMagnitudeSymbol
  unfold h3HeatFourierSymbol
  unfold Real.mulExpNegMulSq

  rw [
    norm_mul,
    Complex.norm_real,
    Complex.norm_real,
    Real.norm_eq_abs,
    Real.norm_eq_abs,
    abs_of_nonneg hx,
    abs_of_pos (Real.exp_pos _)
  ]

  congr 1
  unfold h3FourierGradientMagnitude
  ring_nf

/--
Pointwise one-gradient heat smoothing bound.

The constant is `(sqrt (ν t))⁻¹`; this has exactly the `t⁻¹/²` singularity
needed by the mild time convolution.
-/
theorem norm_h3HeatGradientMagnitudeSymbol_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (ξ : H3FourierPoint3) :
    ‖h3HeatGradientMagnitudeSymbol ν t ξ‖
      ≤
    (Real.sqrt (ν * t))⁻¹ := by
  rw [norm_h3HeatGradientMagnitudeSymbol_eq]
  have hνt : 0 < ν * t := mul_pos hν ht
  have hmul :
      0 ≤
        Real.mulExpNegMulSq
          (ν * t)
          (h3FourierGradientMagnitude ξ) := by
    unfold Real.mulExpNegMulSq
    exact
      mul_nonneg
        (h3FourierGradientMagnitude_nonneg ξ)
        (Real.exp_pos _).le
  rw [← abs_of_nonneg hmul]
  exact Real.abs_mulExpNegMulSq_le hνt

/-! ## Scalar weighted H³ spectral smoothing operator -/

/-- The heat-gradient multiplier preserves `L²` for positive elapsed time. -/
theorem h3HeatGradientFrequency_memLp
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3HeatGradientMagnitudeSymbol ν t ξ * G ξ)
      2 volume := by
  refine
    (MeasureTheory.Lp.memLp G).of_le_mul
      (c := (Real.sqrt (ν * t))⁻¹)
      ?_ ?_
  · exact
      (continuous_h3HeatGradientMagnitudeSymbol ν t).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable G)
  · filter_upwards with ξ
    calc
      ‖h3HeatGradientMagnitudeSymbol ν t ξ * G ξ‖
          =
        ‖h3HeatGradientMagnitudeSymbol ν t ξ‖ * ‖G ξ‖ := by
          rw [norm_mul]
      _ ≤
        (Real.sqrt (ν * t))⁻¹ * ‖G ξ‖ :=
          mul_le_mul_of_nonneg_right
            (norm_h3HeatGradientMagnitudeSymbol_le hν ht ξ)
            (norm_nonneg _)

/--
Apply one radial Fourier gradient and then heat evolution to one weighted
spectral H³ component.
-/
noncomputable def h3SpectralScalarHeatGradientApply
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    H3SpectralScalarState :=
  (h3HeatGradientFrequency_memLp hν ht G).toLp
    (fun ξ : H3FourierPoint3 =>
      h3HeatGradientMagnitudeSymbol ν t ξ * G ξ)

/-- Pointwise representative of the scalar heat-gradient operator. -/
theorem h3SpectralScalarHeatGradientApply_ae
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    (h3SpectralScalarHeatGradientApply
        ν t hν ht G :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      h3HeatGradientMagnitudeSymbol ν t ξ * G ξ) := by
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3HeatGradientFrequency_memLp hν ht G)

/--
One-gradient heat smoothing on one weighted H³ spectral component.
-/
theorem norm_h3SpectralScalarHeatGradientApply_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarHeatGradientApply ν t hν ht G‖
      ≤
    (Real.sqrt (ν * t))⁻¹ * ‖G‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    h3SpectralScalarHeatGradientApply_ae hν ht G
  ] with ξ hξ
  rw [hξ, norm_mul]
  exact
    mul_le_mul_of_nonneg_right
      (norm_h3HeatGradientMagnitudeSymbol_le hν ht ξ)
      (norm_nonneg _)

/-! ## Three-component weighted H³ spectral smoothing operator -/

/-- Coordinatewise heat-gradient smoothing of a weighted H³ velocity state. -/
noncomputable def h3SpectralVelocityHeatGradientApply
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (U : H3SpectralVelocityState) :
    H3SpectralVelocityState :=
  fun j =>
    h3SpectralScalarHeatGradientApply
      ν t hν ht (U j)

@[simp]
theorem h3SpectralVelocityHeatGradientApply_apply
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    h3SpectralVelocityHeatGradientApply
        ν t hν ht U j
      =
    h3SpectralScalarHeatGradientApply
      ν t hν ht (U j) :=
  rfl

/--
Three-component one-gradient heat smoothing in the weighted H³ solver norm.
-/
theorem norm_h3SpectralVelocityHeatGradientApply_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatGradientApply
        ν t hν ht U‖
      ≤
    (Real.sqrt (ν * t))⁻¹ * ‖U‖ := by
  have hc :
      0 ≤ (Real.sqrt (ν * t))⁻¹ := by
    positivity

  apply
    (pi_norm_le_iff_of_nonneg
      (mul_nonneg hc (norm_nonneg U))).2
  intro j

  calc
    ‖h3SpectralVelocityHeatGradientApply
        ν t hν ht U j‖
        ≤
      (Real.sqrt (ν * t))⁻¹ * ‖U j‖ :=
        norm_h3SpectralScalarHeatGradientApply_le
          hν ht (U j)
    _ ≤
      (Real.sqrt (ν * t))⁻¹ * ‖U‖ :=
        mul_le_mul_of_nonneg_left
          (h3SpectralVelocity_coordinate_norm_le U j)
          hc

end

end Euclidean
end Bridge
end PrimeTensor
