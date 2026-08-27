import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SelectedForcingFirst
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedFrozenFubini

/-!
# Frozen terminal contribution for the third Duhamel spatial derivative

The positive-time bootstrap has now produced one spare raw Fourier moment on
the selected unheated nonlinear forcing.

For the third spatial derivative, the frozen terminal forcing contribution is
therefore no longer singular after source-time integration.  Indeed

    |ξ|³ e^{-c ν (t-s)|ξ|²}
      =
    |ξ| · (|ξ|² e^{-c ν (t-s)|ξ|²}),

and the second heat moment integrates exactly in source time with a
viscosity-only coefficient.  The remaining factor is precisely the first raw
Fourier moment of the frozen terminal forcing, already proved integrable in
`SelectedForcingFirst`.

This file closes the frozen half-tail contribution at the product-measure
level and then upgrades the radial bound to arbitrary mixed third coordinate
Fourier derivatives.

The only remaining endpoint issue after this file is the source-state
variation `N(W(s),W(s)) - N(W(t),W(t))` in the stronger first-moment topology.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedThirdDuhamelFrozenEndpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The frozen terminal radial third-moment kernel on the terminal half is
integrable on frequency × source time. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenThirdMoment_halfTail_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun p : H3FourierPoint3 × ℝ =>
        (‖p.1‖ ^ 3 * ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i p.1‖)
      ((volume : Measure H3FourierPoint3).prod
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence (W t) (W t) i

  let f : H3FourierPoint3 × ℝ → ℝ :=
    fun p =>
      (‖p.1‖ ^ 3 * ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) *
        ‖N p.1‖

  let cInv : ℝ := ((2 * Real.pi) ^ 2 * ν)⁻¹

  have hhalf : t / 2 ≤ t := by
    linarith

  have hc : 0 < (2 * Real.pi) ^ 2 * ν := by
    positivity

  have hcInv0 : 0 ≤ cInv := by
    dsimp only [cInv]
    exact inv_nonneg.mpr hc.le

  have hN :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hN1 :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hHeatFactorContinuous :
      Continuous
        (fun p : H3FourierPoint3 × ℝ =>
          ‖p.1‖ ^ 3 * ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) := by
    unfold h3HeatFourierSymbol
    fun_prop

  have hJoint :
      AEStronglyMeasurable
        f
        ((volume : Measure H3FourierPoint3).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
    have hHeatMeas :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ =>
            ‖p.1‖ ^ 3 * ‖h3HeatFourierSymbol ν (t - p.2) p.1‖)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) :=
      hHeatFactorContinuous.aestronglyMeasurable

    have hNMeas :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ => ‖N p.1‖)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) :=
      hN.norm.aestronglyMeasurable.comp_fst

    dsimp only [f]
    exact hHeatMeas.mul hNMeas

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          cInv * (‖ξ‖ * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hN1.const_mul cInv

  refine (integrable_prod_iff hJoint).2 ?_
  constructor

  · exact Filter.Eventually.of_forall fun ξ => by
      have hSecCont :
          Continuous (fun s : ℝ => f (ξ, s)) := by
        dsimp only [f]
        unfold h3HeatFourierSymbol
        fun_prop

      have hSecInterval :
          IntervalIntegrable
            (fun s : ℝ => f (ξ, s))
            volume
            (t / 2)
            t :=
        hSecCont.intervalIntegrable (t / 2) t

      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf] at hSecInterval
      rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hSecInterval
      exact hSecInterval

  · have hOuterMeas :
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            ∫ s : ℝ, ‖f (ξ, s)‖
              ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
          (volume : Measure H3FourierPoint3) :=
      hJoint.norm.integral_prod_right'

    refine hMajorantInt.mono' hOuterMeas ?_
    filter_upwards with ξ

    have hInnerEq :
        (∫ s : ℝ, ‖f (ξ, s)‖
            ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
          =
        ∫ s in (t / 2)..t,
          ‖ξ‖ ^ 3 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
      rw [intervalIntegral.integral_of_le hhalf]
      rw [← restrict_Ioo_eq_restrict_Ioc]
      apply integral_congr_ae
      filter_upwards with s
      dsimp only [f]

      have hf0 :
          0 ≤
            (‖ξ‖ ^ 3 * ‖h3HeatFourierSymbol ν (t - s) ξ‖) *
              ‖N ξ‖ := by
        positivity

      rw [Real.norm_eq_abs, abs_of_nonneg hf0]
      rw [norm_mul]
      ring

    have hThirdEq :
        (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 3 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
          =
        ‖ξ‖ *
          (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖) := by
      calc
        (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 3 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
            =
          ∫ s in (t / 2)..t,
            (‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖) * ‖ξ‖ := by
            apply intervalIntegral.integral_congr
            intro s _hs
            ring
        _ =
          (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖) * ‖ξ‖ := by
            rw [intervalIntegral.integral_mul_const]
        _ =
          ‖ξ‖ *
            (∫ s in (t / 2)..t,
              ‖ξ‖ ^ 2 *
                ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖) := by
            ring

    have hSecondBound :
        (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
          ≤
        cInv * ‖N ξ‖ := by
      dsimp only [cInv, N, W]
      exact
        h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeIntegral_le
          hν U₀ hA hU₀ ht i ξ

    have hThirdBound :
        (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 3 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
          ≤
        cInv * (‖ξ‖ * ‖N ξ‖) := by
      rw [hThirdEq]
      calc
        ‖ξ‖ *
            (∫ s in (t / 2)..t,
              ‖ξ‖ ^ 2 *
                ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
            ≤
          ‖ξ‖ * (cInv * ‖N ξ‖) :=
        mul_le_mul_of_nonneg_left hSecondBound (norm_nonneg _)
        _ = cInv * (‖ξ‖ * ‖N ξ‖) := by
          ring

    have hInnerNonneg :
        0 ≤
          ∫ s in (t / 2)..t,
            ‖ξ‖ ^ 3 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
      exact
        intervalIntegral.integral_nonneg hhalf
          (fun _ _ => by positivity)

    rw [hInnerEq, Real.norm_eq_abs, abs_of_nonneg hInnerNonneg]
    exact hThirdBound

/-- Fourier amplitude for a mixed third coordinate derivative of one
positive-lag nonlinear forcing coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j k l : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol j ξ *
    (h3FourierDerivativeSymbol k ξ *
      (h3FourierDerivativeSymbol l ξ *
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ))

/-- Three coordinate derivative symbols cost at most `(2π)^3 |ξ|^3`. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude_le_thirdMoment
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j k l : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
        ν τ U V i j k l ξ‖
      ≤
    (2 * Real.pi) ^ 3 *
      (‖ξ‖ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ‖) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
  rw [norm_mul, norm_mul, norm_mul]

  have hj :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ
  have hk :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude k ξ
  have hl :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude l ξ

  have hN :
      0 ≤
        ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ‖ :=
    norm_nonneg _

  calc
    ‖h3FourierDerivativeSymbol j ξ‖ *
        (‖h3FourierDerivativeSymbol k ξ‖ *
          (‖h3FourierDerivativeSymbol l ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖))
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol k ξ‖ *
          (‖h3FourierDerivativeSymbol l ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_right
            hj
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hN))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol l ξ‖ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hk
              (mul_nonneg (norm_nonneg _) hN))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hl hN)
              (by
                unfold h3FourierGradientMagnitude
                positivity))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
    _ =
      (2 * Real.pi) ^ 3 *
        (‖ξ‖ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

/-- The frozen mixed third-coordinate Fourier amplitude is integrable on the
frequency/source-time half-tail product. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenThirdCoordinate_halfTail_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j k l : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun p : H3FourierPoint3 × ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          ν (t - p.2) (W t) (W t) i j k l p.1)
      ((volume : Measure H3FourierPoint3).prod
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let M : H3FourierPoint3 × ℝ → ℝ :=
    fun p =>
      (2 * Real.pi) ^ 3 *
        ((‖p.1‖ ^ 3 * ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i p.1‖)

  have hRadial :=
    h3RawFinLerayOuterProductDivergenceHeat_frozenThirdMoment_halfTail_fubini_integrable
      hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        M
        ((volume : Measure H3FourierPoint3).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
    dsimp only [M, W]
    exact hRadial.const_mul ((2 * Real.pi) ^ 3)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun p : H3FourierPoint3 × ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
            ν (t - p.2) (W t) (W t) i j k l p.1)
        ((volume : Measure H3FourierPoint3).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative

    have hj :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ =>
            h3FourierDerivativeSymbol j p.1)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) :=
      (h3FourierDerivativeSymbol_continuous j).aestronglyMeasurable.comp_fst

    have hk :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ =>
            h3FourierDerivativeSymbol k p.1)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) :=
      (h3FourierDerivativeSymbol_continuous k).aestronglyMeasurable.comp_fst

    have hl :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ =>
            h3FourierDerivativeSymbol l p.1)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) :=
      (h3FourierDerivativeSymbol_continuous l).aestronglyMeasurable.comp_fst

    have hHeat :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ =>
            h3HeatFourierSymbol ν (t - p.2) p.1)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
      exact
        (by
          unfold h3HeatFourierSymbol
          fun_prop :
          Continuous
            (fun p : H3FourierPoint3 × ℝ =>
              h3HeatFourierSymbol ν (t - p.2) p.1)).aestronglyMeasurable

    have hN :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ =>
            h3RawFinLerayOuterProductDivergence
              (W t) (W t) i p.1)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) :=
      (h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i).aestronglyMeasurable.comp_fst

    exact hj.mul (hk.mul (hl.mul (hHeat.mul hN)))

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards with p

  have hBound :=
    norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude_le_thirdMoment
      ν (t - p.2) (W t) (W t) i j k l p.1

  dsimp only [M]
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative at hBound
  rw [norm_mul] at hBound

  simpa only [mul_assoc] using hBound

end
end Euclidean
end Bridge
end PrimeTensor
