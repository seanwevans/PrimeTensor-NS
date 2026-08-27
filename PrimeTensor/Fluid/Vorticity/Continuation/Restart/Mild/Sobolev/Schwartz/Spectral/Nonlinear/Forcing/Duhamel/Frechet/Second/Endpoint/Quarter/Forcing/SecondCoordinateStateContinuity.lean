import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SecondCoordinateLagContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.ProfileStateDifference

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter FourierTransform
open scoped ENNReal NNReal Topology Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSecondCoordinateStateContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

theorem norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_diagonal_sub_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ U U i j k x -
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ V V i j k x‖
      ≤
    ((2 * Real.pi) ^ 2 *
      ((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 2) *
      (h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
        h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖) := by
  let KU : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
      ν τ U U i j k x
  let KV : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
      ν τ V V i j k x

  have hKU : Integrable KU (volume : Measure H3FourierPoint3) := by
    dsimp only [KU]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_integrable
        hν hτ U U i j k x

  have hKV : Integrable KV (volume : Measure H3FourierPoint3) := by
    dsimp only [KV]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_integrable
        hν hτ V V i j k x

  let R : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν τ ξ *
          (h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ)‖

  have hR : Integrable R (volume : Measure H3FourierPoint3) := by
    dsimp only [R]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_diagonalDifference_secondMoment_integrable
        hν hτ U V i

  have hM :
      Integrable
        (fun ξ : H3FourierPoint3 => (2 * Real.pi) ^ 2 * R ξ)
        (volume : Measure H3FourierPoint3) :=
    hR.const_mul ((2 * Real.pi) ^ 2)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖KU ξ - KV ξ‖ ≤ (2 * Real.pi) ^ 2 * R ξ := by
    intro ξ
    dsimp only [KU, KV, R]
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
    rw [← smul_sub]
    simp only [Circle.norm_smul]
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative

    have hAlg :
        h3FourierDerivativeSymbol j ξ *
              (h3FourierDerivativeSymbol k ξ *
                (h3HeatFourierSymbol ν τ ξ *
                  h3RawFinLerayOuterProductDivergence U U i ξ)) -
            h3FourierDerivativeSymbol j ξ *
              (h3FourierDerivativeSymbol k ξ *
                (h3HeatFourierSymbol ν τ ξ *
                  h3RawFinLerayOuterProductDivergence V V i ξ))
          =
        h3FourierDerivativeSymbol j ξ *
          (h3FourierDerivativeSymbol k ξ *
            (h3HeatFourierSymbol ν τ ξ *
              (h3RawFinLerayOuterProductDivergence U U i ξ -
                h3RawFinLerayOuterProductDivergence V V i ξ))) := by
      ring

    rw [hAlg, norm_mul, norm_mul]

    have hj :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ
    have hk :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude k ξ
    have hD :
        0 ≤
          ‖h3HeatFourierSymbol ν τ ξ *
            (h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ)‖ :=
      norm_nonneg _

    calc
      ‖h3FourierDerivativeSymbol j ξ‖ *
          (‖h3FourierDerivativeSymbol k ξ‖ *
            ‖h3HeatFourierSymbol ν τ ξ *
              (h3RawFinLerayOuterProductDivergence U U i ξ -
                h3RawFinLerayOuterProductDivergence V V i ξ)‖)
          ≤
        h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol k ξ‖ *
            ‖h3HeatFourierSymbol ν τ ξ *
              (h3RawFinLerayOuterProductDivergence U U i ξ -
                h3RawFinLerayOuterProductDivergence V V i ξ)‖) := by
        exact
          mul_le_mul_of_nonneg_right
            hj
            (mul_nonneg (norm_nonneg _) hD)
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            ‖h3HeatFourierSymbol ν τ ξ *
              (h3RawFinLerayOuterProductDivergence U U i ξ -
                h3RawFinLerayOuterProductDivergence V V i ξ)‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hk hD)
            (by
              unfold h3FourierGradientMagnitude
              positivity)
      _ =
        (2 * Real.pi) ^ 2 *
          (‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν τ ξ *
              (h3RawFinLerayOuterProductDivergence U U i ξ -
                h3RawFinLerayOuterProductDivergence V V i ξ)‖) := by
        unfold h3FourierGradientMagnitude
        ring

  rw [
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_eq_integral_kernel,
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_eq_integral_kernel
  ]

  calc
    ‖(∫ ξ : H3FourierPoint3, KU ξ) -
        ∫ ξ : H3FourierPoint3, KV ξ‖
        =
      ‖∫ ξ : H3FourierPoint3, KU ξ - KV ξ‖ := by
        rw [integral_sub hKU hKV]
    _ ≤
      ∫ ξ : H3FourierPoint3, ‖KU ξ - KV ξ‖ :=
        norm_integral_le_integral_norm _
    _ ≤
      ∫ ξ : H3FourierPoint3, (2 * Real.pi) ^ 2 * R ξ := by
        refine integral_mono_ae (hKU.sub hKV).norm hM ?_
        exact Filter.Eventually.of_forall hPoint
    _ =
      (2 * Real.pi) ^ 2 *
        (∫ ξ : H3FourierPoint3, R ξ) := by
        rw [integral_const_mul]
    _ ≤
      (2 * Real.pi) ^ 2 *
        (((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 2 *
          (h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
            h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (by
              dsimp only [R]
              exact
                h3RawFinLerayOuterProductDivergenceHeat_diagonalDifference_secondMoment_integral_le_stateDifference
                  hν hτ U V i)
            (sq_nonneg (2 * Real.pi))
    _ =
      ((2 * Real.pi) ^ 2 *
        ((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 2) *
        (h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
          h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖) := by
        ring

end
end Euclidean
end Bridge
end PrimeTensor
