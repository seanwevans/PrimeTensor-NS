import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Frequency.Trichotomy.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.F.Deriv.Coordinate.Bound

/-!
# BKM endpoint: low/high localized gradient Fourier mass

The exact trichotomy factors are pointwise contractions.  This file turns that
algebra into the analytic objects needed by the endpoint proof.

For an arbitrary weighted H³ scalar state `G` and derivative coordinate `i`,
define

    D_i G(ξ) = d_i(ξ) G_raw(ξ),

together with its low- and high-frequency localizations

    χ_low(ξ) D_i G(ξ),
    χ_high(ξ) D_i G(ξ).

The existing H³ first-moment estimate gives the reusable quantitative bound

    ∫ ‖D_i G(ξ)‖ dξ
      ≤ C_C1 ‖G‖.

Since the low and high multipliers have norm at most one, both localized
amplitudes are integrable with the same `L¹` bound.  Their ordinary inverse
Fourier integrals are therefore pointwise bounded by the same quantity.

This is deliberately the non-sharp common bound.  The next files can sharpen
the low piece using its compact support and the high piece using its exterior
support without reopening the measurability/integrability layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointFrequencyTrichotomyGradientMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Continuity of the endpoint trichotomy factors -/

theorem h3BKMDyadicLowFrequencyFactor_continuous
    (lo : ℕ) :
    Continuous
      (h3BKMDyadicLowFrequencyFactor lo) := by

  unfold h3BKMDyadicLowFrequencyFactor

  exact
    (
      h3BKMFrequencyCutoffBump_contDiff
        (h3BKMDyadicRadius_pos lo)
    ).continuous

theorem h3BKMDyadicHighFrequencyFactor_continuous
    (hi : ℕ) :
    Continuous
      (h3BKMDyadicHighFrequencyFactor hi) := by

  unfold h3BKMDyadicHighFrequencyFactor

  exact
    continuous_const.sub
      (
        h3BKMFrequencyCutoffBump_contDiff
          (h3BKMDyadicRadius_pos (hi + 1))
      ).continuous

/-! ## Localized raw Fourier gradients -/

/-- Low-frequency localization of one raw H³ Fourier derivative. -/
noncomputable def h3BKMLowGradientAmplitude
    (lo : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ℂ :=
  (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)
    *
  h3SpectralScalarRawFourierCoordinateDerivative
    G i ξ

/-- High-frequency localization of one raw H³ Fourier derivative. -/
noncomputable def h3BKMHighGradientAmplitude
    (hi : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ℂ :=
  (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)
    *
  h3SpectralScalarRawFourierCoordinateDerivative
    G i ξ

/--
Reusable quantitative `L¹` estimate for one raw Fourier coordinate derivative
of an arbitrary H³ spectral scalar state.
-/
theorem integral_norm_h3SpectralScalarRawFourierCoordinateDerivative_le
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
      ‖h3SpectralScalarRawFourierCoordinateDerivative G i ξ‖)
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      * ‖G‖ := by

  have hDerivativeInt :
      Integrable
        (h3SpectralScalarRawFourierCoordinateDerivative G i)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourierCoordinateDerivative_integrable
      G i

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourier_firstMoment_integrable G

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi)
            *
          (‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul
      (2 * Real.pi)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourierCoordinateDerivative G i ξ‖
          ≤
        (2 * Real.pi)
          *
        (‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖) := by

    intro ξ

    unfold h3SpectralScalarRawFourierCoordinateDerivative

    calc
      ‖h3FourierDerivativeSymbol i ξ
          *
        h3SpectralScalarRawFourier G ξ‖
          =
        ‖h3FourierDerivativeSymbol i ξ‖
          *
        ‖h3SpectralScalarRawFourier G ξ‖ := by
            rw [norm_mul]

      _ ≤
        h3FourierGradientMagnitude ξ
          *
        ‖h3SpectralScalarRawFourier G ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_h3FourierDerivativeSymbol_le_gradientMagnitude i ξ)
          (norm_nonneg _)

      _ =
        (2 * Real.pi)
          *
        (‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖) := by
          unfold h3FourierGradientMagnitude
          ring

  calc
    (∫ ξ : H3FourierPoint3,
      ‖h3SpectralScalarRawFourierCoordinateDerivative G i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi)
          *
        (‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖) := by

          exact
            integral_mono_ae
              hDerivativeInt.norm
              hMajorantInt
              (Filter.Eventually.of_forall hPoint)

    _ =
      (2 * Real.pi)
        *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖) := by
          rw [integral_const_mul]

    _ ≤
      (2 * Real.pi)
        *
      (
        h3SobolevFirstMomentDeweightingConstant
          * ‖G‖
      ) := by
          exact
            mul_le_mul_of_nonneg_left
              (h3SpectralScalarRawFourier_firstMoment_integral_le G)
              (by positivity)

    _ =
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        * ‖G‖ := by
          unfold
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
          ring

/-! ## Integrability of the localized pieces -/

theorem h3BKMLowGradientAmplitude_integrable
    (lo : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    Integrable
      (h3BKMLowGradientAmplitude lo G i)
      (volume : Measure H3FourierPoint3) := by

  have hDerivativeInt :
      Integrable
        (h3SpectralScalarRawFourierCoordinateDerivative G i)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourierCoordinateDerivative_integrable
      G i

  have hFactorMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ))
        (volume : Measure H3FourierPoint3) :=
    (
      Complex.continuous_ofReal.comp
        (h3BKMDyadicLowFrequencyFactor_continuous lo)
    ).aestronglyMeasurable

  apply
    hDerivativeInt.norm.mono'
      (hFactorMeas.mul hDerivativeInt.aestronglyMeasurable)

  filter_upwards with ξ

  simp only [Pi.mul_apply]

  exact
    norm_h3BKMDyadicLowFrequencyFactor_mul_le
      lo ξ
      (h3SpectralScalarRawFourierCoordinateDerivative G i ξ)

theorem h3BKMHighGradientAmplitude_integrable
    (hi : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    Integrable
      (h3BKMHighGradientAmplitude hi G i)
      (volume : Measure H3FourierPoint3) := by

  have hDerivativeInt :
      Integrable
        (h3SpectralScalarRawFourierCoordinateDerivative G i)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourierCoordinateDerivative_integrable
      G i

  have hFactorMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ))
        (volume : Measure H3FourierPoint3) :=
    (
      Complex.continuous_ofReal.comp
        (h3BKMDyadicHighFrequencyFactor_continuous hi)
    ).aestronglyMeasurable

  apply
    hDerivativeInt.norm.mono'
      (hFactorMeas.mul hDerivativeInt.aestronglyMeasurable)

  filter_upwards with ξ

  simp only [Pi.mul_apply]

  exact
    norm_h3BKMDyadicHighFrequencyFactor_mul_le
      hi ξ
      (h3SpectralScalarRawFourierCoordinateDerivative G i ξ)

/-! ## Quantitative localized `L¹` bounds -/

theorem integral_norm_h3BKMLowGradientAmplitude_le
    (lo : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
      ‖h3BKMLowGradientAmplitude lo G i ξ‖)
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      * ‖G‖ := by

  have hLowInt :=
    h3BKMLowGradientAmplitude_integrable
      lo G i

  have hDerivativeInt :=
    h3SpectralScalarRawFourierCoordinateDerivative_integrable
      G i

  calc
    (∫ ξ : H3FourierPoint3,
      ‖h3BKMLowGradientAmplitude lo G i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourierCoordinateDerivative G i ξ‖ := by

          exact
            integral_mono_ae
              hLowInt.norm
              hDerivativeInt.norm
              (
                Filter.Eventually.of_forall
                  (fun ξ =>
                    norm_h3BKMDyadicLowFrequencyFactor_mul_le
                      lo ξ
                      (h3SpectralScalarRawFourierCoordinateDerivative
                        G i ξ))
              )

    _ ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        * ‖G‖ :=
      integral_norm_h3SpectralScalarRawFourierCoordinateDerivative_le
        G i

theorem integral_norm_h3BKMHighGradientAmplitude_le
    (hi : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
      ‖h3BKMHighGradientAmplitude hi G i ξ‖)
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      * ‖G‖ := by

  have hHighInt :=
    h3BKMHighGradientAmplitude_integrable
      hi G i

  have hDerivativeInt :=
    h3SpectralScalarRawFourierCoordinateDerivative_integrable
      G i

  calc
    (∫ ξ : H3FourierPoint3,
      ‖h3BKMHighGradientAmplitude hi G i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourierCoordinateDerivative G i ξ‖ := by

          exact
            integral_mono_ae
              hHighInt.norm
              hDerivativeInt.norm
              (
                Filter.Eventually.of_forall
                  (fun ξ =>
                    norm_h3BKMDyadicHighFrequencyFactor_mul_le
                      hi ξ
                      (h3SpectralScalarRawFourierCoordinateDerivative
                        G i ξ))
              )

    _ ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        * ‖G‖ :=
      integral_norm_h3SpectralScalarRawFourierCoordinateDerivative_le
        G i

/-! ## Pointwise inverse-Fourier bounds -/

theorem norm_fourierInv_h3BKMLowGradientAmplitude_le
    (lo : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖FourierTransformInv.fourierInv
        (h3BKMLowGradientAmplitude lo G i)
        x‖
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      * ‖G‖ := by

  calc
    ‖FourierTransformInv.fourierInv
        (h3BKMLowGradientAmplitude lo G i)
        x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖h3BKMLowGradientAmplitude lo G i ξ‖ := by

          change
            ‖VectorFourier.fourierIntegral
                Real.fourierChar
                (volume : Measure H3FourierPoint3)
                (-(innerₗ H3FourierPoint3))
                (h3BKMLowGradientAmplitude lo G i)
                x‖
              ≤
            ∫ ξ : H3FourierPoint3,
              ‖h3BKMLowGradientAmplitude lo G i ξ‖

          exact
            VectorFourier.norm_fourierIntegral_le_integral_norm
              Real.fourierChar
              (volume : Measure H3FourierPoint3)
              (-(innerₗ H3FourierPoint3))
              (h3BKMLowGradientAmplitude lo G i)
              x

    _ ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        * ‖G‖ :=
      integral_norm_h3BKMLowGradientAmplitude_le
        lo G i

theorem norm_fourierInv_h3BKMHighGradientAmplitude_le
    (hi : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖FourierTransformInv.fourierInv
        (h3BKMHighGradientAmplitude hi G i)
        x‖
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      * ‖G‖ := by

  calc
    ‖FourierTransformInv.fourierInv
        (h3BKMHighGradientAmplitude hi G i)
        x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖h3BKMHighGradientAmplitude hi G i ξ‖ := by

          change
            ‖VectorFourier.fourierIntegral
                Real.fourierChar
                (volume : Measure H3FourierPoint3)
                (-(innerₗ H3FourierPoint3))
                (h3BKMHighGradientAmplitude hi G i)
                x‖
              ≤
            ∫ ξ : H3FourierPoint3,
              ‖h3BKMHighGradientAmplitude hi G i ξ‖

          exact
            VectorFourier.norm_fourierIntegral_le_integral_norm
              Real.fourierChar
              (volume : Measure H3FourierPoint3)
              (-(innerₗ H3FourierPoint3))
              (h3BKMHighGradientAmplitude hi G i)
              x

    _ ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        * ‖G‖ :=
      integral_norm_h3BKMHighGradientAmplitude_le
        hi G i

end

end Euclidean
end Bridge
end PrimeTensor
