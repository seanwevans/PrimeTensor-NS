import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.Input.Difference.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Heat.Derivative.Continuity

/-!
# Positive-lag continuity of the pointwise nonlinear derivative kernel

The retarded derivative-path continuity argument has already been split into
three pieces.  The two input-variation pieces are quantitatively controlled by
bilinearity.  This file closes the remaining frozen-input lag-variation term.

For a fixed positive base lag `τ₀`, put `a = τ₀ / 2`.  Every nearby lag
`τ > a` factors as

    τ = a + (τ - a).

The heat semigroup identity therefore writes the Fourier derivative amplitude
at lag `τ` as an additional nonnegative-time heat multiplier applied to the
fixed amplitude at lag `a`.  That extra multiplier has norm at most one, so
the fixed-lag derivative integrand at `a` is an `L¹` dominator.  Dominated
convergence then gives continuity of the ordinary inverse-Fourier derivative
representative at every strictly positive lag.

Composing with `s ↦ t - s` gives exactly the frozen-input retarded continuity
term required by the three-term decomposition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter FourierTransform
open scoped ENNReal NNReal Topology Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathDerivativeLagContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fourier-integral kernel whose integral is the classical first spatial
coordinate derivative representative. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x ξ : H3FourierPoint3) : ℂ :=
  𝐞 (-(inner ℝ ξ (-x))) •
    (h3FourierDerivativeSymbol j ξ *
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U V i ξ)

/-- At every positive lag, the classical derivative Fourier kernel is
integrable. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_integrable
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    Integrable
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
        ν τ U V i j x)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
  rw [Real.fourierIntegral_convergent_iff (-x)]
  exact
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
      hν hτ U V i j

/-- If `a > 0` and `a ≤ τ`, the derivative Fourier kernel at lag `τ` is
pointwise dominated in norm by the same kernel at the fixed earlier lag `a`.
This is the semigroup domination used by dominated convergence. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_le_of_le
    {ν a τ : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (haτ : a ≤ τ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x ξ : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
        ν τ U V i j x ξ‖
      ≤
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
        ν a U V i j x ξ‖ := by
  have hb : 0 ≤ τ - a :=
    sub_nonneg.mpr haτ
  have hsplit : a + (τ - a) = τ := by
    ring
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

  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
  simp only [Circle.norm_smul]
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  rw [hheat]

  calc
    ‖h3FourierDerivativeSymbol j ξ *
        ((h3HeatFourierSymbol ν (τ - a) ξ *
            h3HeatFourierSymbol ν a ξ) *
          h3RawFinLerayOuterProductDivergence U V i ξ)‖
        =
      ‖h3FourierDerivativeSymbol j ξ‖ *
        (‖h3HeatFourierSymbol ν (τ - a) ξ‖ *
          (‖h3HeatFourierSymbol ν a ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)) := by
          simp only [norm_mul]
          ring
    _ ≤
      ‖h3FourierDerivativeSymbol j ξ‖ *
        (1 *
          (‖h3HeatFourierSymbol ν a ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                hcontract
                (mul_nonneg
                  (norm_nonneg _)
                  (norm_nonneg _)))
              (norm_nonneg _)
    _ =
      ‖h3FourierDerivativeSymbol j ξ *
        (h3HeatFourierSymbol ν a ξ *
          h3RawFinLerayOuterProductDivergence U V i ξ)‖ := by
          simp only [norm_mul, one_mul]

/-- For each fixed frequency and spatial point, the derivative Fourier kernel
is continuous in the heat lag. -/
theorem continuous_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_lag
    (ν : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x ξ : H3FourierPoint3) :
    Continuous
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
          ν τ U V i j x ξ) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  unfold h3HeatFourierSymbol
  fun_prop

/-- The classical inverse-Fourier derivative representative is literally the
integral of the Fourier kernel introduced above. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_eq_integral_kernel
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j x
      =
    ∫ ξ : H3FourierPoint3,
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
        ν τ U V i j x ξ := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourier_eq]
  rfl

/-- For fixed spectral inputs and a fixed spatial point, the classical first
spatial derivative representative is continuous at every strictly positive
heat lag. -/
theorem continuousAt_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_lag
    {ν τ₀ : ℝ}
    (hν : 0 < ν)
    (hτ₀ : 0 < τ₀)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ U V i j x)
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
          ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
              ν a U V i j x ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_integrable
      hν ha U V i j x).norm

  have hIntegral :
      Tendsto
        (fun τ : ℝ =>
          ∫ ξ : H3FourierPoint3,
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
              ν τ U V i j x ξ)
        (𝓝 τ₀)
        (𝓝
          (∫ ξ : H3FourierPoint3,
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
              ν τ₀ U V i j x ξ)) := by
    exact
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (l := 𝓝 τ₀)
        (F := fun τ : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
            ν τ U V i j x)
        (f :=
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
            ν τ₀ U V i j x)
        (bound := fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
              ν a U V i j x ξ‖)
        (by
          filter_upwards [hnear] with τ hτ
          have hτpos : 0 < τ := lt_trans ha hτ
          exact
            (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_integrable
              hν hτpos U V i j x).aestronglyMeasurable)
        (by
          filter_upwards [hnear] with τ hτ
          exact
            Eventually.of_forall fun ξ =>
              norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_le_of_le
                hν ha hτ.le U V i j x ξ)
        hBoundInt
        (Eventually.of_forall fun ξ =>
          (continuous_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel_lag
            ν U V i j x ξ).continuousAt)

  show Tendsto
    (fun τ : ℝ =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j x)
    (𝓝 τ₀)
    (𝓝
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ₀ U V i j x))
  simpa only [
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_eq_integral_kernel
  ] using hIntegral

/-- The frozen-input retarded derivative representative is continuous at every
interior source time `s₀ < t`.  This is precisely the third term in the
three-term retarded difference decomposition. -/
theorem continuousAt_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_retarded_frozen
    {ν t s₀ : ℝ}
    (hν : 0 < ν)
    (hs₀ : s₀ < t)
    (U₀ V₀ : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν (t - s) U₀ V₀ i j x)
      s₀ := by
  have hLag :
      ContinuousAt (fun s : ℝ => t - s) s₀ :=
    continuousAt_const.sub continuousAt_id
  exact
    (continuousAt_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_lag
      hν (sub_pos.mpr hs₀) U₀ V₀ i j x).comp hLag

end

end Euclidean
end Bridge
end PrimeTensor
