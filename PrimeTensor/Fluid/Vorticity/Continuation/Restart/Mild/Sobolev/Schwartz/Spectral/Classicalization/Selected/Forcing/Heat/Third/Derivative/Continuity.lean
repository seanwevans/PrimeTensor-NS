import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Heat.Third.Derivative.Endpoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Classicalization: selected forcing third-derivative heat continuity

At a fixed selected positive restart time the zero-lag third-coordinate
forcing reconstruction has already been identified with the genuine third
spatial Fréchet derivative.

The remaining fixed-state endpoint statement is strong continuity as the heat
lag tends to zero from the right.

Three coordinate multipliers are dominated by the integrable cubic raw Fourier
moment, while the heat symbol is contractive on nonnegative times.  Dominated
convergence therefore gives

    D_a D_b D_c H_τ N(W(t),W(t))(x)
      ⟶
    D³N(W(t),W(t))(x)[e_a,e_b,e_c]

as `τ ↓ 0`.

No moving-state estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology Real RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingHeatThirdDerivativeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At a fixed selected positive time, the positive-lag ordered
third-coordinate forcing reconstruction converges from the right to the
corresponding genuine third Fréchet derivative of the instantaneous forcing. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
          ν τ (W t) (W t) i a b c x)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        (iteratedFDeriv ℝ 3
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c)
          ])) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun τ ξ =>
      phase ξ *
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          ν τ (W t) (W t) i a b c ξ

  let f0 : H3FourierPoint3 → ℂ :=
    fun ξ =>
      phase ξ *
        (h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ *
              h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ)))

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          (h3FourierDerivativeSymbol c ξ *
            h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ))‖

  have hPhaseContinuous :
      Continuous phase := by
    dsimp only [phase]
    fun_prop

  have hFMeas :
      ∀ᶠ τ : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        AEStronglyMeasurable
          (F τ)
          (volume : Measure H3FourierPoint3) := by
    exact
      Filter.Eventually.of_forall
        (fun τ => by
          dsimp only [F]
          unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          exact
            hPhaseContinuous.aestronglyMeasurable.mul
              ((h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
                ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
                  ((h3FourierDerivativeSymbol_continuous c).aestronglyMeasurable.mul
                    (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
                      ν τ (W t) (W t) i)))))

  have hBoundAE :
      ∀ᶠ τ : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
          ‖F τ ξ‖ ≤ bound ξ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    filter_upwards with ξ

    have hHeat :
        ‖h3HeatFourierSymbol ν τ ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one hν.le hτ ξ

    have hPhaseNorm :
        ‖phase ξ‖ = 1 := by
      dsimp only [phase]
      simp only [
        Complex.norm_exp,
        Complex.mul_re,
        Complex.ofReal_re,
        Complex.ofReal_im,
        Complex.I_re,
        Complex.I_im,
        mul_zero,
        zero_mul,
        sub_self,
        Real.exp_zero
      ]

    dsimp only [F, bound]
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
    rw [norm_mul, hPhaseNorm, one_mul, norm_mul, norm_mul, norm_mul, norm_mul]

    calc
      ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3FourierDerivativeSymbol c ξ‖ *
              (‖h3HeatFourierSymbol ν τ ξ‖ *
                ‖h3RawFinLerayOuterProductDivergence
                  (W t) (W t) i ξ‖)))
          ≤
        ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3FourierDerivativeSymbol c ξ‖ *
              (1 *
                ‖h3RawFinLerayOuterProductDivergence
                  (W t) (W t) i ξ‖))) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right
                    hHeat
                    (norm_nonneg _))
                  (norm_nonneg _))
                (norm_nonneg _))
              (norm_nonneg _)
      _ =
        ‖h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ *
              h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ))‖ := by
          rw [one_mul, norm_mul, norm_mul, norm_mul]

  have hBoundInt :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    dsimp only [bound, W]
    exact
      (h3RawFinLerayOuterProductDivergence_selectedRestart_thirdCoordinate_integrable
        hν U₀ hA hU₀ ht htR i a b c).norm

  have hLim :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Tendsto
          (fun τ : ℝ => F τ ξ)
          (𝓝[Set.Ici (0 : ℝ)] 0)
          (𝓝 (f0 ξ)) := by
    filter_upwards with ξ

    have hRaw :=
      tendsto_h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero_right
        (ν := ν) (W t) (W t) i ξ

    dsimp only [F, f0]
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    exact
      tendsto_const_nhds.mul
        (tendsto_const_nhds.mul
          (tendsto_const_nhds.mul
            (tendsto_const_nhds.mul hRaw)))

  have hMain :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure H3FourierPoint3))
      (l := (𝓝[Set.Ici (0 : ℝ)] 0))
      (F := F)
      (f := f0)
      bound
      hFMeas
      hBoundAE
      hBoundInt
      hLim

  have hPathEq :
      (fun τ : ℝ =>
        ∫ ξ : H3FourierPoint3, F τ ξ)
        =
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
          ν τ (W t) (W t) i a b c x) := by
    funext τ
    dsimp only [F, phase]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hLimitEq :
      (∫ ξ : H3FourierPoint3, f0 ξ)
        =
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
        ν 0 (W t) (W t) i a b c x := by
    dsimp only [f0, phase]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
    unfold
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W t) (W t) i
    ]
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  rw [hPathEq, hLimitEq] at hMain

  have hEndpoint :=
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
      hν U₀ hA hU₀ ht htR i a b c x

  dsimp only at hEndpoint
  rw [hEndpoint] at hMain

  exact hMain

end

end Euclidean
end Bridge
end PrimeTensor
