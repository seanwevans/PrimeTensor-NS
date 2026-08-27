import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedProfileFullIntegral
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.L1.Bound

/-!
# Mixed coordinate second derivatives of the positive-lag forcing kernel

The first-derivative path spent one Fourier moment.  The selected endpoint
analysis has now closed genuine time integrability of the full second Fourier
moment.  This file converts two concrete Fourier derivative symbols into that
radial second moment.

For coordinate directions `j,k`,

    |D_j(ξ) D_k(ξ)| <= (2π)^2 |ξ|^2.

Consequently the mixed second-derivative Fourier amplitude is genuinely L1 at
every positive heat lag, and its classical inverse-Fourier representative is
pointwise bounded by `(2π)^2` times the radial second-moment mass.

This is the fixed-lag analytic input needed before the mixed second spatial
derivative can be passed through the Duhamel source-time integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform
open scoped ENNReal NNReal Topology Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSecondCoordinate
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fourier amplitude for a mixed coordinate second derivative of one
positive-lag nonlinear forcing coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol j ξ *
    (h3FourierDerivativeSymbol k ξ *
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U V i ξ)

/-- Two coordinate Fourier derivative symbols cost at most the radial second
moment, with the exact Euclidean factor `(2π)^2`. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_le_secondMoment
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
        ν τ U V i j k ξ‖
      ≤
    (2 * Real.pi) ^ 2 *
      (‖ξ‖ ^ 2 *
        ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ‖) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
  rw [norm_mul, norm_mul]

  have hj :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ
  have hk :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude k ξ

  have hN :
      0 ≤
        ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ‖ :=
    norm_nonneg _

  calc
    ‖h3FourierDerivativeSymbol j ξ‖ *
        (‖h3FourierDerivativeSymbol k ξ‖ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖)
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol k ξ‖ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖) := by
      exact
        mul_le_mul_of_nonneg_right
          hj
          (mul_nonneg (norm_nonneg _) hN)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hk hN)
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ =
      (2 * Real.pi) ^ 2 *
        (‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖) := by
      unfold h3FourierGradientMagnitude
      ring

/-- The mixed second-coordinate Fourier amplitude is genuinely integrable at
every positive heat lag. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_integrable
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3) :
    Integrable
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
        ν τ U V i j k)
      (volume : Measure H3FourierPoint3) := by
  have hTargetMeas :
      AEStronglyMeasurable
        (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
          ν τ U V i j k)
        (volume : Measure H3FourierPoint3) := by
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous j).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous k).aestronglyMeasurable.mul
          (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
            ν τ U V i))

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ U V i 2 (by norm_num)

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 2 *
            (‖ξ‖ ^ 2 *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ U V i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul ((2 * Real.pi) ^ 2)

  refine hMajorantInt.mono' hTargetMeas ?_
  filter_upwards with ξ

  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_le_secondMoment
      ν τ U V i j k ξ

/-- The L1 mass of a mixed second-coordinate Fourier amplitude is bounded by
`(2π)^2` times the radial second Fourier moment. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_norm_integral_le_secondMoment
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
          ν τ U V i j k ξ‖)
      ≤
    (2 * Real.pi) ^ 2 *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖) := by
  have hTargetInt :=
    (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_integrable
      hν hτ U V i j k).norm

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
      hν hτ U V i 2 (by norm_num)

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 2 *
            (‖ξ‖ ^ 2 *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ U V i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul ((2 * Real.pi) ^ 2)

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
          ν τ U V i j k ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) ^ 2 *
          (‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖) := by
      refine integral_mono_ae hTargetInt hMajorantInt ?_
      filter_upwards with ξ
      exact
        norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_le_secondMoment
          ν τ U V i j k ξ
    _ =
      (2 * Real.pi) ^ 2 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖) := by
      rw [integral_const_mul]

/-- Classical inverse-Fourier representative of a mixed coordinate second
derivative of one positive-lag nonlinear forcing coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3) : ℂ :=
  FourierTransformInv.fourierInv
    (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
      ν τ U V i j k)
    x

/-- Fourier inversion turns the mixed second-coordinate L1 mass into a uniform
pointwise bound. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_le_secondMoment
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i j k x‖
      ≤
    (2 * Real.pi) ^ 2 *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourier_eq]

  calc
    ‖∫ ξ : H3FourierPoint3,
        𝐞 (-(inner ℝ ξ (-x))) •
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
            ν τ U V i j k ξ‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖𝐞 (-(inner ℝ ξ (-x))) •
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
            ν τ U V i j k ξ‖ :=
      norm_integral_le_integral_norm _
    _ =
      ∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
          ν τ U V i j k ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [Circle.norm_smul]
    _ ≤
      (2 * Real.pi) ^ 2 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖) :=
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_norm_integral_le_secondMoment
        hν hτ U V i j k

end

end Euclidean
end Bridge
end PrimeTensor
