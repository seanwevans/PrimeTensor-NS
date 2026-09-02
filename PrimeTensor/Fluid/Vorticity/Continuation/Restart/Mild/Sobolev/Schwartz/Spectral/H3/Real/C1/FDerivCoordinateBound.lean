import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.FDerivCoordinate
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1.Bound

/-!
# Quantitative H³ coordinate-derivative evaluation bound

For every weighted H³ scalar spectral state `G`, the canonical inverse-Fourier
representative is `C¹`.  The preceding coordinate theorem identifies

    D_a C¹(G)(x)
      =
    𝓕⁻(d_a G_raw)(x).

The nonlinear forcing `L¹` layer already supplies the quantitative H³
first-moment estimate

    ∫ ‖ξ‖ ‖G_raw(ξ)‖ dξ
      ≤
    C_H3,1 ‖G‖.

Combining the uniform Fourier-integral bound with
`‖d_a(ξ)‖ ≤ 2π ‖ξ‖` yields the reusable evaluation estimate

    ‖D_a C¹(G)(x)‖
      ≤
    (2π C_H3,1) ‖G‖.

This is the boundedness input needed to package coordinate derivative
evaluation as a continuous linear functional on H³ and commute it through
Bochner Duhamel integrals.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3RealC1FDerivCoordinateBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fixed operator bound for one coordinate derivative evaluation of the
canonical H³ `C¹` inverse-Fourier representative. -/
def h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient : ℝ :=
  (2 * Real.pi) * h3SobolevFirstMomentDeweightingConstant

theorem h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg :
    0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient := by
  unfold h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  positivity [h3SobolevFirstMomentDeweightingConstant_nonneg]

/-- One coordinate derivative evaluation of the canonical H³ `C¹`
representative is bounded uniformly in the spatial point by the H³ norm. -/
theorem norm_h3SpectralScalarC1Representative_fderiv_apply_fin_le
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖(fderiv ℝ
        (h3SpectralScalarC1Representative G)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 i))‖
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * ‖G‖ := by
  rw [h3SpectralScalarC1Representative_fderiv_apply_fin]

  let D : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourierCoordinateDerivative G i

  let M : H3FourierPoint3 → ℝ :=
    fun ξ =>
      (2 * Real.pi) *
        (‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖)

  have hDInt :
      Integrable D
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralScalarRawFourierCoordinateDerivative_integrable
        G i

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourier_firstMoment_integrable G

  have hMInt :
      Integrable M
        (volume : Measure H3FourierPoint3) := by
    dsimp only [M]
    exact hMoment.const_mul (2 * Real.pi)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖D ξ‖ ≤ M ξ := by
    intro ξ
    dsimp only [D, M]
    unfold h3SpectralScalarRawFourierCoordinateDerivative
    calc
      ‖h3FourierDerivativeSymbol i ξ *
          h3SpectralScalarRawFourier G ξ‖
          =
        ‖h3FourierDerivativeSymbol i ξ‖ *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
            rw [norm_mul]
      _ ≤
        h3FourierGradientMagnitude ξ *
          ‖h3SpectralScalarRawFourier G ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_h3FourierDerivativeSymbol_le_gradientMagnitude i ξ)
          (norm_nonneg _)
      _ =
        (2 * Real.pi) *
          (‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖) := by
            unfold h3FourierGradientMagnitude
            ring

  have hIntegral :
      (∫ ξ : H3FourierPoint3, ‖D ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, M ξ := by
    exact
      integral_mono_ae
        hDInt.norm
        hMInt
        (Filter.Eventually.of_forall hPoint)

  have hFourier :
      ‖FourierTransformInv.fourierInv D x‖
        ≤
      ∫ ξ : H3FourierPoint3, ‖D ξ‖ := by
    change
      ‖VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          D
          x‖
        ≤
      ∫ ξ : H3FourierPoint3, ‖D ξ‖
    exact
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        D
        x

  have hFirst :=
    h3SpectralScalarRawFourier_firstMoment_integral_le G

  calc
    ‖FourierTransformInv.fourierInv D x‖
        ≤
      ∫ ξ : H3FourierPoint3, ‖D ξ‖ :=
      hFourier
    _ ≤
      ∫ ξ : H3FourierPoint3, M ξ :=
      hIntegral
    _ =
      (2 * Real.pi) *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖) := by
      dsimp only [M]
      rw [integral_const_mul]
    _ ≤
      (2 * Real.pi) *
        (h3SobolevFirstMomentDeweightingConstant * ‖G‖) := by
      exact
        mul_le_mul_of_nonneg_left
          hFirst
          (by positivity)
    _ =
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖G‖ := by
      unfold h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      ring

end

end Euclidean
end Bridge
end PrimeTensor
