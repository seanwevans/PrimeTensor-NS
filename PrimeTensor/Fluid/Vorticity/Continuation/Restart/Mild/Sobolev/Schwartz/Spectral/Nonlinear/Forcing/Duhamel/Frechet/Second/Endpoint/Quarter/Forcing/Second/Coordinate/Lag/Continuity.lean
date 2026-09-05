import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SecondCoordinate

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter FourierTransform
open scoped ENNReal NNReal Topology Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSecondCoordinateLagContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable def h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x ξ : H3FourierPoint3) : ℂ :=
  𝐞 (-(inner ℝ ξ (-x))) •
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
      ν τ U V i j k ξ

theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_integrable
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    Integrable
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
        ν τ U V i j k x)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
  rw [Real.fourierIntegral_convergent_iff (-x)]
  exact
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_integrable
      hν hτ U V i j k

theorem norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_le_of_le
    {ν a τ : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (haτ : a ≤ τ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x ξ : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
        ν τ U V i j k x ξ‖
      ≤
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
        ν a U V i j k x ξ‖ := by
  have hb : 0 ≤ τ - a := sub_nonneg.mpr haτ
  have hsplit : a + (τ - a) = τ := by ring
  have hheat :
      h3HeatFourierSymbol ν τ ξ
        =
      h3HeatFourierSymbol ν (τ - a) ξ *
        h3HeatFourierSymbol ν a ξ := by
    simpa only [hsplit] using
      (h3HeatFourierSymbol_add ν a (τ - a) ξ)
  have hcontract :
      ‖h3HeatFourierSymbol ν (τ - a) ξ‖ ≤ 1 :=
    norm_h3HeatFourierSymbol_le_one hν.le hb ξ

  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
  simp only [Circle.norm_smul]
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  rw [hheat]

  calc
    ‖h3FourierDerivativeSymbol j ξ *
        (h3FourierDerivativeSymbol k ξ *
          ((h3HeatFourierSymbol ν (τ - a) ξ *
              h3HeatFourierSymbol ν a ξ) *
            h3RawFinLerayOuterProductDivergence U V i ξ))‖
        =
      ‖h3FourierDerivativeSymbol j ξ‖ *
        (‖h3FourierDerivativeSymbol k ξ‖ *
          (‖h3HeatFourierSymbol ν (τ - a) ξ‖ *
            (‖h3HeatFourierSymbol ν a ξ‖ *
              ‖h3RawFinLerayOuterProductDivergence U V i ξ‖))) := by
      simp only [norm_mul]
      ring
    _ ≤
      ‖h3FourierDerivativeSymbol j ξ‖ *
        (‖h3FourierDerivativeSymbol k ξ‖ *
          (1 *
            (‖h3HeatFourierSymbol ν a ξ‖ *
              ‖h3RawFinLerayOuterProductDivergence U V i ξ‖))) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hcontract
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
            (norm_nonneg _))
          (norm_nonneg _)
    _ =
      ‖h3FourierDerivativeSymbol j ξ *
        (h3FourierDerivativeSymbol k ξ *
          (h3HeatFourierSymbol ν a ξ *
            h3RawFinLerayOuterProductDivergence U V i ξ))‖ := by
      simp only [norm_mul, one_mul]

theorem continuous_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_lag
    (ν : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x ξ : H3FourierPoint3) :
    Continuous
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
          ν τ U V i j k x ξ) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  unfold h3HeatFourierSymbol
  fun_prop

theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_eq_integral_kernel
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i j k x
      =
    ∫ ξ : H3FourierPoint3,
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
        ν τ U V i j k x ξ := by
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourier_eq]
  rfl

theorem continuousAt_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_lag
    {ν τ₀ : ℝ}
    (hν : 0 < ν)
    (hτ₀ : 0 < τ₀)
    (U V : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ U V i j k x)
      τ₀ := by
  let a : ℝ := τ₀ / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have haτ₀ : a < τ₀ := by
    dsimp [a]
    linarith
  have hnear : Set.Ioi a ∈ 𝓝 τ₀ :=
    Ioi_mem_nhds haτ₀

  have hBoundInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
              ν a U V i j k x ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_integrable
      hν ha U V i j k x).norm

  have hIntegral :
      Tendsto
        (fun τ : ℝ =>
          ∫ ξ : H3FourierPoint3,
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
              ν τ U V i j k x ξ)
        (𝓝 τ₀)
        (𝓝
          (∫ ξ : H3FourierPoint3,
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
              ν τ₀ U V i j k x ξ)) := by
    exact
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (l := 𝓝 τ₀)
        (F := fun τ : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
            ν τ U V i j k x)
        (f :=
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
            ν τ₀ U V i j k x)
        (bound := fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
              ν a U V i j k x ξ‖)
        (by
          filter_upwards [hnear] with τ hτ
          have hτpos : 0 < τ := lt_trans ha hτ
          exact
            (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_integrable
              hν hτpos U V i j k x).aestronglyMeasurable)
        (by
          filter_upwards [hnear] with τ hτ
          exact
            Filter.Eventually.of_forall fun ξ =>
              norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_le_of_le
                hν ha hτ.le U V i j k x ξ)
        hBoundInt
        (Filter.Eventually.of_forall fun ξ =>
          (continuous_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel_lag
            ν U V i j k x ξ).continuousAt)

  show Tendsto
    (fun τ : ℝ =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i j k x)
    (𝓝 τ₀)
    (𝓝
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ₀ U V i j k x))
  simpa only [
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_eq_integral_kernel
  ] using hIntegral

theorem continuousAt_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_retarded_frozen
    {ν t s₀ : ℝ}
    (hν : 0 < ν)
    (hs₀ : s₀ < t)
    (U₀ V₀ : H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν (t - s) U₀ V₀ i j k x)
      s₀ := by
  have hLag :
      ContinuousAt (fun s : ℝ => t - s) s₀ :=
    continuousAt_const.sub continuousAt_id
  exact
    (continuousAt_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_lag
      hν (sub_pos.mpr hs₀) U₀ V₀ i j k x).comp hLag

end
end Euclidean
end Bridge
end PrimeTensor
