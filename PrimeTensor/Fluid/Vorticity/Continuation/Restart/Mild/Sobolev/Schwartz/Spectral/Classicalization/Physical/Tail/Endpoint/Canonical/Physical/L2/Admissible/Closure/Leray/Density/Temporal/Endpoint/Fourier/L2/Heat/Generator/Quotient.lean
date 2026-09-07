import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Heat.Generator.Representative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Physical L² temporal admissibility: heat-generator right quotient

The previous endpoint layer identifies the quotient-safe heat generator with
the exact time-generator Fourier multiplier.  To pass from that multiplier
identity to an `L²` derivative, we first isolate the scalar raw Fourier
difference quotient.

For one weighted H³ scalar state `G`, define

    Q_h(ξ) =
      h⁻¹ • (m(h,ξ) raw(G)(ξ) - raw(G)(ξ)).

The pointwise right limit at `h = 0` is the heat generator

    -ν q(ξ) raw(G)(ξ).

The mean-value inequality gives the uniform positive-increment bound

    ‖Q_h(ξ)‖ ≤ ‖-ν q(ξ) raw(G)(ξ)‖.

Because the right-hand side is exactly the quotient-safe Laplacian density,
this is the domination needed for the next `L²` dominated-convergence step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatGeneratorQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Pointwise raw Fourier heat-generator amplitude at elapsed zero. -/
noncomputable def h3RawFourierL2HeatGeneratorRawAmplitude
    (ν : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℂ :=
  (((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ)) *
    h3SpectralScalarRawFourier G ξ

/-- Positive-increment raw Fourier difference quotient of the heat orbit. -/
noncomputable def h3RawFourierL2HeatQuotientRawAmplitude
    (ν h : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℂ :=
  h⁻¹ •
    (h3HeatFourierSymbol ν h ξ *
        h3SpectralScalarRawFourier G ξ
      -
      h3SpectralScalarRawFourier G ξ)

/-- Frequencywise, the positive heat quotient tends from the right to the
heat generator at elapsed zero. -/
theorem tendsto_h3RawFourierL2HeatQuotientRawAmplitude_zero_right
    (ν : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h3RawFourierL2HeatQuotientRawAmplitude
          ν h G ξ)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3RawFourierL2HeatGeneratorRawAmplitude
          ν G ξ)) := by
  have hDeriv :=
    (h3HeatFourierSymbol_hasDerivAt_time
      ν 0 ξ).mul_const
      (h3SpectralScalarRawFourier G ξ)

  have hSlope :=
    hDeriv.tendsto_slope_zero_right

  have hZero :
      h3HeatFourierSymbol ν 0 ξ *
          h3SpectralScalarRawFourier G ξ
        =
      h3SpectralScalarRawFourier G ξ := by
    unfold h3HeatFourierSymbol
    simp

  have hGenerator :
      h3HeatFourierTimeGeneratorSymbol ν 0 ξ *
          h3SpectralScalarRawFourier G ξ
        =
      h3RawFourierL2HeatGeneratorRawAmplitude
        ν G ξ := by
    rw [h3HeatFourierTimeGeneratorSymbol_eq]
    unfold
      h3RawFourierL2HeatGeneratorRawAmplitude
      h3HeatFourierSymbol
    simp

  rw [hZero, hGenerator] at hSlope

  simpa only [
    zero_add,
    h3RawFourierL2HeatQuotientRawAmplitude
  ] using hSlope

/-- For every positive increment, the raw Fourier heat quotient is dominated
pointwise by the zero-time generator density. -/
theorem norm_h3RawFourierL2HeatQuotientRawAmplitude_le_generator
    {ν h : ℝ}
    (hν : 0 ≤ ν)
    (hh : 0 < h)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3RawFourierL2HeatQuotientRawAmplitude
        ν h G ξ‖
      ≤
    ‖h3RawFourierL2HeatGeneratorRawAmplitude
        ν G ξ‖ := by
  let raw : ℂ :=
    h3SpectralScalarRawFourier G ξ

  let f : ℝ → ℂ :=
    fun r =>
      h3HeatFourierSymbol ν r ξ * raw

  let f' : ℝ → ℂ :=
    fun r =>
      h3HeatFourierTimeGeneratorSymbol ν r ξ * raw

  let C : ℝ :=
    ‖h3RawFourierL2HeatGeneratorRawAmplitude
        ν G ξ‖

  have hDeriv :
      ∀ r ∈ Set.Icc (0 : ℝ) h,
        HasDerivWithinAt
          f
          (f' r)
          (Set.Icc (0 : ℝ) h)
          r := by
    intro r hr
    dsimp only [f, f', raw]
    exact
      ((h3HeatFourierSymbol_hasDerivAt_time
        ν r ξ).mul_const
        (h3SpectralScalarRawFourier G ξ)).hasDerivWithinAt

  have hBound :
      ∀ r ∈ Set.Ico (0 : ℝ) h,
        ‖f' r‖ ≤ C := by
    intro r hr

    have hm :
        ‖h3HeatFourierSymbol ν r ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one
        hν hr.1 ξ

    dsimp only [f', C, raw]
    rw [h3HeatFourierTimeGeneratorSymbol_eq]
    unfold h3RawFourierL2HeatGeneratorRawAmplitude
    rw [norm_mul, norm_mul, norm_mul]

    have hCoeff :
        0 ≤
          ‖(((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ))‖ :=
      norm_nonneg _

    calc
      ‖(((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ))‖ *
            ‖h3HeatFourierSymbol ν r ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖
          ≤
        ‖(((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ))‖ *
            1 *
            ‖h3SpectralScalarRawFourier G ξ‖ := by
              exact
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hm hCoeff)
                  (norm_nonneg _)
      _ =
        ‖(((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ))‖ *
            ‖h3SpectralScalarRawFourier G ξ‖ := by
              rw [mul_one]

  have hIncrement :
      ‖f h - f 0‖ ≤ C * (h - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      hDeriv
      hBound
      h
      ⟨hh.le, le_rfl⟩

  have hInvNonneg :
      0 ≤ h⁻¹ :=
    inv_nonneg.mpr hh.le

  have hQuotient :
      ‖h⁻¹ • (f h - f 0)‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]

    calc
      h⁻¹ * ‖f h - f 0‖
          ≤
        h⁻¹ * (C * (h - 0)) :=
          mul_le_mul_of_nonneg_left
            hIncrement hInvNonneg
      _ = C := by
        rw [sub_zero]
        calc
          h⁻¹ * (C * h)
              =
            (h⁻¹ * h) * C := by ring
          _ = C := by
            simp [ne_of_gt hh]

  unfold h3RawFourierL2HeatQuotientRawAmplitude
  dsimp only [f, raw] at hQuotient
  simpa [h3HeatFourierSymbol, C] using hQuotient

end

end Euclidean
end Bridge
end PrimeTensor
