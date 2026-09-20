import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C2.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Coordinate.Second
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Endpoint.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Classicalization: selected forcing second-derivative heat endpoint

The second-Fréchet fresh-tail rescaling reduces the next Duhamel endpoint
problem to the behavior, as the heat lag tends to zero, of one ordered mixed
second spatial coordinate of

    H_τ N(W(t), W(t)).

At a selected positive restart time the unheated forcing already has an
integrable second raw Fourier moment.  Thus the zero-lag multiplier

    d_a(ξ) d_b(ξ) N̂(W(t),W(t))(ξ)

is integrable, reconstructs the genuine second Fréchet derivative of the
unheated forcing, and dominates the positive-lag heat multipliers because the
heat symbol is contractive.

This is the order-two counterpart of
`Selected.Forcing.Heat.First.Derivative.Endpoint`.

The repeated moment-to-coordinate reconstruction pattern here is intentionally
kept visible: together with the existing order-one/three/four constructions it
is a candidate for later order-generic extraction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology Real RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingHeatSecondDerivativeEndpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At a selected positive restart time, two coordinate multipliers of the
unheated raw forcing are genuinely Fourier `L¹`. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_secondCoordinate_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ))
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  have hZero :
      Integrable F
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hSecond :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ * F ξ))
        (volume : Measure H3FourierPoint3) :=
    (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
      ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
        hZero.aestronglyMeasurable)

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 2 *
            (‖ξ‖ ^ 2 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hSecond.const_mul ((2 * Real.pi) ^ 2)

  refine hMajorant.mono' hTargetMeas ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [norm_mul, norm_mul]
    have ha :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
    have hb :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ
    calc
      ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ * ‖F ξ‖)
          ≤
        h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol b ξ‖ * ‖F ξ‖) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ * ‖F ξ‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
      _ =
        (2 * Real.pi) ^ 2 *
          (‖ξ‖ ^ 2 * ‖F ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

/-- At zero heat lag, the mixed second-coordinate reconstruction is exactly
the genuine second Fréchet derivative of the selected unheated forcing on the
same ordered pair of canonical directions. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν 0 (W t) (W t) i a b x
      =
    iteratedFDeriv ℝ 2
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ] := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 2 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b)
    ]

  have hZero :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hFirst :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hSecond :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMom :
      ∀ (n : ℕ), n ≤ (2 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn2 : n ≤ 2 := by
      exact_mod_cast hn
    have hnCases :
        n = 0 ∨ n = 1 ∨ n = 2 := by
      omega
    rcases hnCases with rfl | rfl | rfl
    · simpa only [pow_zero, one_mul] using hZero.norm
    · simpa only [pow_one] using hFirst
    · exact hSecond

  have hMeas :
      AEStronglyMeasurable
        f
        (volume : Measure H3FourierPoint3) :=
    hZero.aestronglyMeasurable

  have hDeriv :=
    VectorFourier.iteratedFDeriv_fourierIntegral
      (L := L)
      (f := f)
      (μ := (volume : Measure H3FourierPoint3))
      hMom
      hMeas
      (n := 2)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hRawEq :
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 2 m)
        =
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ * f ξ)) := by
    funext ξ

    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)

    have ha :
        h3FourierDerivativeSymbol a ξ
          =
        ((2 * Real.pi * inner ℝ ξ ea : ℝ) : ℂ) *
          Complex.I := by
      dsimp only [ea]
      rw [h3FourierDerivativeSymbol_eq_inner]
      push_cast
      ring

    have hb :
        h3FourierDerivativeSymbol b ξ
          =
        ((2 * Real.pi * inner ℝ ξ eb : ℝ) : ℂ) *
          Complex.I := by
      dsimp only [eb]
      rw [h3FourierDerivativeSymbol_eq_inner]
      push_cast
      ring

    dsimp only [L, m]
    simp only [
      VectorFourier.fourierPowSMulRight_apply,
      Fin.prod_univ_two,
      neg_apply,
      innerSL_apply_apply ℝ,
      smul_eq_mul
    ]
    rw [ha, hb]
    dsimp only [ea, eb]
    simp only [Complex.real_smul]
    push_cast
    ring

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 2)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 2 (by norm_num))
      hMeas

  rw [
    Real.fourierIntegral_continuousMultilinearMap_apply'
      hPowInt
  ] at hEval

  rw [hRawEq] at hEval

  have hHeatZero :
      (fun ξ : H3FourierPoint3 =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
          ν 0 (W t) (W t) i a b ξ)
        =
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ * f ξ)) := by
    funext ξ
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W t) (W t) i
    ]

  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
  change
    FourierTransformInv.fourierInv
      (fun ξ : H3FourierPoint3 =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
          ν 0 (W t) (W t) i a b ξ)
      x
      =
    iteratedFDeriv ℝ 2
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ]
  rw [hHeatZero]

  unfold h3RawFinLerayOuterProductDivergenceC0Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ * f ξ))
        x
      =
    iteratedFDeriv ℝ 2
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x
      m

  exact hEval.symm

/-- At a fixed selected positive time, the positive-lag mixed second-coordinate
forcing reconstruction converges from the right to the corresponding genuine
second Fréchet derivative of the instantaneous forcing. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ (W t) (W t) i a b x)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        (iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b)
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
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
          ν τ (W t) (W t) i a b ξ

  let f0 : H3FourierPoint3 → ℂ :=
    fun ξ =>
      phase ξ *
        (h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ))

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ)‖

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
          unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
          exact
            hPhaseContinuous.aestronglyMeasurable.mul
              ((h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
                ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
                  (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
                    ν τ (W t) (W t) i))))

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
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
    rw [norm_mul, hPhaseNorm, one_mul, norm_mul, norm_mul, norm_mul]

    calc
      ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3HeatFourierSymbol ν τ ξ‖ *
              ‖h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ‖))
          ≤
        ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (1 *
              ‖h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ‖)) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hHeat
                  (norm_nonneg _))
                (norm_nonneg _))
              (norm_nonneg _)
      _ =
        ‖h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ)‖ := by
          rw [one_mul, norm_mul, norm_mul]

  have hBoundInt :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    dsimp only [bound, W]
    exact
      (h3RawFinLerayOuterProductDivergence_selectedRestart_secondCoordinate_integrable
        hν U₀ hA hU₀ ht htR i a b).norm

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
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    exact
      tendsto_const_nhds.mul
        (tendsto_const_nhds.mul
          (tendsto_const_nhds.mul hRaw))

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
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ (W t) (W t) i a b x) := by
    funext τ
    dsimp only [F, phase]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hLimitEq :
      (∫ ξ : H3FourierPoint3, f0 ξ)
        =
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν 0 (W t) (W t) i a b x := by
    dsimp only [f0, phase]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W t) (W t) i
    ]
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  rw [hPathEq, hLimitEq] at hMain

  have hEndpoint :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
      hν U₀ hA hU₀ ht htR i a b x

  dsimp only at hEndpoint
  rw [hEndpoint] at hMain

  exact hMain

end

end Euclidean
end Bridge
end PrimeTensor
