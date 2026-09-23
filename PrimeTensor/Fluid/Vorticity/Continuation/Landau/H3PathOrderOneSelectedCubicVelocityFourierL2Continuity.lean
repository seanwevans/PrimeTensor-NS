import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedStrongL2FromCoefficientContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedDuhamelTailCubicL2Baseline
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Third.Jet.Continuity

/-!
# Strong Fourier L² continuity of selected cubic velocity coordinates

The last order-one frontier is strong physical `L²` continuity of

    ∂ₐ ∂ₜ Sⱼ
      = Σₖ ∂ₐ ∂ₖ ∂ₖ Sⱼ - ∂ₐ Nⱼ.

This file closes the topology of the cubic velocity part on the Fourier side.

For an arbitrary weighted H³ scalar state `G`, package the ordered cubic
coordinate multiplier

    dₐ(ξ) d_b(ξ) d_c(ξ) raw(G)(ξ)

as a genuine Fourier `L²` state.

The exact H³ weight already gives

    |ξ|³ W₃(ξ)⁻¹ ≤ 1,

while each coordinate derivative symbol is bounded by `2π |ξ|`.  Hence the
packaged map is `(2π)^3`-Lipschitz:

    ‖D̂ₐD̂_bD̂_c(G) - D̂ₐD̂_bD̂_c(H)‖₂
      ≤ (2π)^3 ‖G-H‖₂.

Therefore composing with the globally continuous selected weighted H³ spectral
path immediately gives strong Fourier `L²` continuity of every ordered cubic
selected velocity coordinate.

The next transport is only the already-standard inverse Fourier / real-part /
`Point3` pipeline.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedCubicVelocityFourierL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The ordered cubic coordinate raw amplitude of one weighted H³ scalar
state belongs to Fourier `L²`. -/
theorem h3SpectralScalarRawThirdCoordinate_memLp2
    (a b c : PrimeTensor.Axis Depth.three)
    (G : H3SpectralScalarState) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis a) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis b) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis c) ξ *
              h3SpectralScalarRawFourier G ξ)))
      2
      (volume : Measure H3FourierPoint3) := by
  let third : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        (h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ *
            h3SpectralScalarRawFourier G ξ))

  have hThirdMeas :
      AEStronglyMeasurable third
        (volume : Measure H3FourierPoint3) := by
    dsimp only [third]
    exact
      (h3FourierDerivativeSymbol_continuous
        (h3ClassicalizationFinOfAxis a)).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis b)).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous
            (h3ClassicalizationFinOfAxis c)).aestronglyMeasurable.mul
            (h3SpectralScalarRawFourier_memLp2 G).1))

  have hRadial :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
            h3SpectralScalarRawFourier G ξ)
        2
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourier_cubicWeight_memLp2 G

  refine
    hRadial.of_le_mul
      (c := (2 * Real.pi) ^ 3)
      hThirdMeas
      ?_

  filter_upwards with ξ

  rw [norm_mul, norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis a) ξ

  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis b) ξ

  have hc :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis c) ξ

  have hGrad0 :
      0 ≤ h3FourierGradientMagnitude ξ := by
    unfold h3FourierGradientMagnitude
    positivity

  calc
    ‖h3FourierDerivativeSymbol
        (h3ClassicalizationFinOfAxis a) ξ‖ *
        (‖h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis b) ξ‖ *
          (‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖))
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis b) ξ‖ *
          (‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg
            (norm_nonneg _)
            (mul_nonneg
              (norm_nonneg _)
              (norm_nonneg _)))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hb
            (mul_nonneg
              (norm_nonneg _)
              (norm_nonneg _)))
          hGrad0
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            ‖h3SpectralScalarRawFourier G ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hc
              (norm_nonneg _))
            hGrad0)
          hGrad0
    _ =
      (2 * Real.pi) ^ 3 *
        ‖((‖ξ‖ ^ 3 : ℝ) : ℂ) *
          h3SpectralScalarRawFourier G ξ‖ := by
      unfold h3FourierGradientMagnitude
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 3)]
      ring

/-- Quotient-safe Fourier `L²` package for one ordered cubic coordinate of a
weighted H³ scalar state. -/
noncomputable def h3SpectralScalarRawThirdCoordinateFourierL2
    (a b c : PrimeTensor.Axis Depth.three)
    (G : H3SpectralScalarState) :
    H3FourierComplexL2 :=
  (h3SpectralScalarRawThirdCoordinate_memLp2 a b c G).toLp
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        (h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ *
            h3SpectralScalarRawFourier G ξ)))

/-- The cubic coordinate package has its literal multiplier as a.e.
representative. -/
theorem h3SpectralScalarRawThirdCoordinateFourierL2_ae
    (a b c : PrimeTensor.Axis Depth.three)
    (G : H3SpectralScalarState) :
    ((h3SpectralScalarRawThirdCoordinateFourierL2 a b c G :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        (h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ *
            h3SpectralScalarRawFourier G ξ))) := by
  exact
    MemLp.coeFn_toLp
      (h3SpectralScalarRawThirdCoordinate_memLp2
        a b c G)

/-- Spending three ordered coordinate derivatives costs at most `(2π)^3` in
the weighted H³ spectral norm. -/
theorem norm_h3SpectralScalarRawThirdCoordinateFourierL2_le
    (a b c : PrimeTensor.Axis Depth.three)
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarRawThirdCoordinateFourierL2 a b c G‖
      ≤
    (2 * Real.pi) ^ 3 * ‖G‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

  filter_upwards [
    h3SpectralScalarRawThirdCoordinateFourierL2_ae
      a b c G
  ] with ξ hξ

  rw [hξ]

  have hInv0 :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact
      inv_nonneg.mpr
        (h3SobolevFrequencyWeight_pos ξ).le

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis a) ξ

  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis b) ξ

  have hc :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis c) ξ

  have hGrad0 :
      0 ≤ h3FourierGradientMagnitude ξ := by
    unfold h3FourierGradientMagnitude
    positivity

  have hRadial :=
    h3FourierNorm_cubed_mul_h3SobolevFrequencyWeightInv_le_one ξ

  unfold
    h3SpectralScalarRawFourier
    h3SobolevFrequencyWeightInvComplex

  rw [
    norm_mul,
    norm_mul,
    norm_mul,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hInv0
  ]

  calc
    ‖h3FourierDerivativeSymbol
        (h3ClassicalizationFinOfAxis a) ξ‖ *
        (‖h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis b) ξ‖ *
          (‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ‖ *
            (h3SobolevFrequencyWeightInv ξ * ‖G ξ‖)))
        ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (h3SobolevFrequencyWeightInv ξ * ‖G ξ‖))) := by
      gcongr
    _ =
      (2 * Real.pi) ^ 3 *
        ((‖ξ‖ ^ 3 *
          h3SobolevFrequencyWeightInv ξ) * ‖G ξ‖) := by
      unfold h3FourierGradientMagnitude
      ring
    _ ≤
      (2 * Real.pi) ^ 3 * (1 * ‖G ξ‖) := by
      gcongr
    _ =
      (2 * Real.pi) ^ 3 * ‖G ξ‖ := by
      ring

/-- The cubic coordinate package respects subtraction. -/
theorem h3SpectralScalarRawThirdCoordinateFourierL2_sub
    (a b c : PrimeTensor.Axis Depth.three)
    (G H : H3SpectralScalarState) :
    h3SpectralScalarRawThirdCoordinateFourierL2
        a b c (G - H)
      =
    h3SpectralScalarRawThirdCoordinateFourierL2
        a b c G
      -
    h3SpectralScalarRawThirdCoordinateFourierL2
        a b c H := by
  apply MeasureTheory.Lp.ext

  have hGH :=
    h3SpectralScalarRawThirdCoordinateFourierL2_ae
      a b c (G - H)

  have hG :=
    h3SpectralScalarRawThirdCoordinateFourierL2_ae
      a b c G

  have hH :=
    h3SpectralScalarRawThirdCoordinateFourierL2_ae
      a b c H

  have hRaw :=
    h3SpectralScalarRawFourier_sub_ae G H

  have hOut :=
    MeasureTheory.Lp.coeFn_sub
      (h3SpectralScalarRawThirdCoordinateFourierL2 a b c G)
      (h3SpectralScalarRawThirdCoordinateFourierL2 a b c H)

  filter_upwards [hGH, hG, hH, hRaw, hOut] with
      ξ hGHξ hGξ hHξ hRawξ hOutξ

  rw [hGHξ, hOutξ]
  simp only [Pi.sub_apply]
  rw [hGξ, hHξ, hRawξ]
  ring

/-- Quantitative Lipschitz estimate for the cubic coordinate package. -/
theorem norm_h3SpectralScalarRawThirdCoordinateFourierL2_sub_le
    (a b c : PrimeTensor.Axis Depth.three)
    (G H : H3SpectralScalarState) :
    ‖h3SpectralScalarRawThirdCoordinateFourierL2 a b c G
        -
      h3SpectralScalarRawThirdCoordinateFourierL2 a b c H‖
      ≤
    (2 * Real.pi) ^ 3 * ‖G - H‖ := by
  rw [
    ← h3SpectralScalarRawThirdCoordinateFourierL2_sub
  ]

  exact
    norm_h3SpectralScalarRawThirdCoordinateFourierL2_le
      a b c (G - H)

/-- The ordered cubic coordinate multiplier is strongly continuous from the
weighted H³ scalar state to Fourier `L²`. -/
theorem continuous_h3SpectralScalarRawThirdCoordinateFourierL2
    (a b c : PrimeTensor.Axis Depth.three) :
    Continuous
      (h3SpectralScalarRawThirdCoordinateFourierL2 a b c) := by
  rw [continuous_iff_continuousAt]
  intro G

  unfold ContinuousAt
  rw [tendsto_iff_norm_sub_tendsto_zero]

  apply squeeze_zero

  · intro H
    exact norm_nonneg _

  · intro H
    exact
      norm_h3SpectralScalarRawThirdCoordinateFourierL2_sub_le
        a b c H G

  · have hBound :
        ContinuousAt
          (fun H : H3SpectralScalarState =>
            (2 * Real.pi) ^ 3 * ‖H - G‖)
          G := by
      fun_prop

    simpa using hBound.tendsto

/-- Along the selected restart, every ordered cubic velocity coordinate is
strongly continuous in Fourier `L²` on all real source times. -/
theorem continuous_h3SelectedRestartRawThirdCoordinateFourierL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun s : ℝ =>
        h3SpectralScalarRawThirdCoordinateFourierL2
          a b c
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s i)) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW :
      Continuous W :=
    continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hCoord :
      Continuous
        (fun s : ℝ => W s i) :=
    (continuous_apply i).comp hW

  exact
    (continuous_h3SpectralScalarRawThirdCoordinateFourierL2
      a b c).comp hCoord

end

end Euclidean
end Bridge
end PrimeTensor
