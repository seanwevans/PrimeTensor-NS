import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderTwoSelectedVelocityFourthRadialL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedVelocityFourthCoordinateFourierL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2000000

private noncomputable def h3OrderTwoFourthCoordinateMultiplier
    (a b c d : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3)
    (z : ℂ) : ℂ :=
  h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ *
    (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ *
      (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis c) ξ *
        (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis d) ξ * z)))

private theorem h3OrderTwoFourthCoordinateMultiplier_sub
    (a b c d : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3)
    (z w : ℂ) :
    h3OrderTwoFourthCoordinateMultiplier a b c d ξ (z - w)
      =
    h3OrderTwoFourthCoordinateMultiplier a b c d ξ z
      -
    h3OrderTwoFourthCoordinateMultiplier a b c d ξ w := by
  unfold h3OrderTwoFourthCoordinateMultiplier
  ring

private theorem norm_h3OrderTwoFourthCoordinateMultiplier_le_radial
    (a b c d : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3)
    (z : ℂ) :
    ‖h3OrderTwoFourthCoordinateMultiplier a b c d ξ z‖
      ≤
    (2 * Real.pi) ^ 4 *
      ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) * z‖ := by
  unfold h3OrderTwoFourthCoordinateMultiplier
  rw [norm_mul, norm_mul, norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis a) ξ
  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis b) ξ
  have hc :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis c) ξ
  have hd :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis d) ξ

  have hGrad0 : 0 ≤ h3FourierGradientMagnitude ξ := by
    unfold h3FourierGradientMagnitude
    positivity

  calc
    ‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ‖ *
        (‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ‖ *
          (‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis c) ξ‖ *
            (‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis d) ξ‖ * ‖z‖)))
        ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (h3FourierGradientMagnitude ξ * ‖z‖))) := by
      gcongr
    _ =
      (2 * Real.pi) ^ 4 *
        ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) * z‖ := by
      unfold h3FourierGradientMagnitude
      rw [
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 4)
      ]
      ring


/-- The elementary ordered-symbol product used in this file is exactly the
repository's native selected fourth Fréchet raw coordinate multiplier. -/
private theorem h3OrderTwoFourthCoordinateMultiplier_eq_selectedFrechet
    (H : H3SpectralScalarState)
    (a b c d : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3) :
    h3OrderTwoFourthCoordinateMultiplier a b c d ξ
        (h3SpectralScalarRawFourier H ξ)
      =
    h3SelectedFourthFrechetRawCoordinateMultiplier
      H a b c d ξ := by

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection a
  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection b
  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection c
  let ed : H3FourierPoint3 :=
    h3FourierAxisDirection d

  have ha :
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ
        =
      ((2 * Real.pi * inner ℝ ξ ea : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ea]
    rw [h3FourierDerivativeSymbol_eq_inner]
    rw [h3AxisOfFin3_h3ClassicalizationFinOfAxis]
    push_cast
    ring

  have hb :
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis b) ξ
        =
      ((2 * Real.pi * inner ℝ ξ eb : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [eb]
    rw [h3FourierDerivativeSymbol_eq_inner]
    rw [h3AxisOfFin3_h3ClassicalizationFinOfAxis]
    push_cast
    ring

  have hc :
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis c) ξ
        =
      ((2 * Real.pi * inner ℝ ξ ec : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ec]
    rw [h3FourierDerivativeSymbol_eq_inner]
    rw [h3AxisOfFin3_h3ClassicalizationFinOfAxis]
    push_cast
    ring

  have hd :
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis d) ξ
        =
      ((2 * Real.pi * inner ℝ ξ ed : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ed]
    rw [h3FourierDerivativeSymbol_eq_inner]
    rw [h3AxisOfFin3_h3ClassicalizationFinOfAxis]
    push_cast
    ring

  unfold h3OrderTwoFourthCoordinateMultiplier
  unfold h3SelectedFourthFrechetRawCoordinateMultiplier
  dsimp only

  simp only [
    VectorFourier.fourierPowSMulRight_apply,
    Fin.prod_univ_succ,
    Finset.univ_eq_empty,
    Finset.prod_empty,
    Matrix.cons_val_zero,
    Matrix.cons_val_one,
    Matrix.head_cons,
    Matrix.tail_cons,
    neg_apply,
    innerSL_apply_apply ℝ,
    smul_eq_mul
  ]

  rw [ha, hb, hc, hd]
  dsimp only [ea, eb, ec, ed]
  simp [Complex.real_smul] <;> push_cast <;> ring

theorem h3PreterminalSelectedVelocityFourthCoordinate_memLp2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q : Set.Ioo
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3OrderTwoFourthCoordinateMultiplier a b c d ξ
          (h3SpectralScalarRawFourier (W (q : ℝ) j) ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  have hRadial :
      H3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_closed

  have hMultiplier :
      H3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius_of_radial
      hRadial

  have hM :=
    hMultiplier
      E u T t₀ hNS ht₀ hE hTail
      (q : ℝ) q.property

  dsimp only at hM ⊢

  have hNative :=
    hM.1 a b c d j

  have hAE :
      (fun ξ : H3FourierPoint3 =>
        h3OrderTwoFourthCoordinateMultiplier a b c d ξ
          (h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              (q : ℝ) j) ξ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SelectedFourthFrechetRawCoordinateMultiplier
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          (q : ℝ) j)
        a b c d := by
    filter_upwards with ξ
    exact
      h3OrderTwoFourthCoordinateMultiplier_eq_selectedFrechet
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          (q : ℝ) j)
        a b c d ξ

  exact
    (memLp_congr_ae hAE).2 hNative

noncomputable def h3PreterminalSelectedVelocityFourthCoordinateFourierL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q : Set.Ioo
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three) :
    H3FourierComplexL2 :=
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE
  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
  (h3PreterminalSelectedVelocityFourthCoordinate_memLp2
      hNS ht₀ hE hTail q j a b c d).toLp
    (fun ξ : H3FourierPoint3 =>
      h3OrderTwoFourthCoordinateMultiplier a b c d ξ
        (h3SpectralScalarRawFourier (W (q : ℝ) j) ξ))

theorem h3PreterminalSelectedVelocityFourthCoordinateFourierL2_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q : Set.Ioo
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
    ((h3PreterminalSelectedVelocityFourthCoordinateFourierL2
        hNS ht₀ hE hTail q j a b c d :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3OrderTwoFourthCoordinateMultiplier a b c d ξ
        (h3SpectralScalarRawFourier (W (q : ℝ) j) ξ)) := by
  dsimp only
  unfold h3PreterminalSelectedVelocityFourthCoordinateFourierL2
  exact
    MemLp.coeFn_toLp
      (h3PreterminalSelectedVelocityFourthCoordinate_memLp2
        hNS ht₀ hE hTail q j a b c d)

theorem norm_h3PreterminalSelectedVelocityFourthCoordinateFourierL2_sub_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three)
    (s t : Set.Ioo
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    ‖h3PreterminalSelectedVelocityFourthCoordinateFourierL2
          hNS ht₀ hE hTail s j a b c d
        -
      h3PreterminalSelectedVelocityFourthCoordinateFourierL2
          hNS ht₀ hE hTail t j a b c d‖
      ≤
    (2 * Real.pi) ^ 4 *
      ‖h3PreterminalSelectedVelocityFourthRadialFourierL2
          hNS ht₀ hE hTail s j
        -
        h3PreterminalSelectedVelocityFourthRadialFourierL2
          hNS ht₀ hE hTail t j‖ := by

  let Cs : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFourthCoordinateFourierL2
      hNS ht₀ hE hTail s j a b c d
  let Ct : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFourthCoordinateFourierL2
      hNS ht₀ hE hTail t j a b c d
  let Rs : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFourthRadialFourierL2
      hNS ht₀ hE hTail s j
  let Rt : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFourthRadialFourierL2
      hNS ht₀ hE hTail t j

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail)

  have hCs :=
    h3PreterminalSelectedVelocityFourthCoordinateFourierL2_ae
      hNS ht₀ hE hTail s j a b c d
  have hCt :=
    h3PreterminalSelectedVelocityFourthCoordinateFourierL2_ae
      hNS ht₀ hE hTail t j a b c d
  have hRs :=
    h3PreterminalSelectedVelocityFourthRadialFourierL2_ae
      hNS ht₀ hE hTail s j
  have hRt :=
    h3PreterminalSelectedVelocityFourthRadialFourierL2_ae
      hNS ht₀ hE hTail t j
  have hCsub := MeasureTheory.Lp.coeFn_sub Cs Ct
  have hRsub := MeasureTheory.Lp.coeFn_sub Rs Rt

  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

  filter_upwards [
    hCs, hCt, hRs, hRt, hCsub, hRsub
  ] with ξ hCsξ hCtξ hRsξ hRtξ hCsubξ hRsubξ

  rw [hCsubξ, hRsubξ]
  simp only [Pi.sub_apply]
  rw [hCsξ, hCtξ, hRsξ, hRtξ]
  unfold h3SelectedRawFourierFourthRadialWeight
  rw [← h3OrderTwoFourthCoordinateMultiplier_sub]
  rw [← mul_sub]

  exact
    norm_h3OrderTwoFourthCoordinateMultiplier_le_radial
      a b c d ξ
      (h3SpectralScalarRawFourier
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail)
            (s : ℝ) j) ξ
        -
       h3SpectralScalarRawFourier
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail)
            (t : ℝ) j) ξ)

theorem continuous_h3PreterminalSelectedVelocityFourthCoordinateFourierL2OnRestartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q : Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedVelocityFourthCoordinateFourierL2
          hNS ht₀ hE hTail q j a b c d) := by

  let F4 :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        H3FourierComplexL2 :=
    fun q =>
      h3PreterminalSelectedVelocityFourthRadialFourierL2
        hNS ht₀ hE hTail q j

  let C4 :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        H3FourierComplexL2 :=
    fun q =>
      h3PreterminalSelectedVelocityFourthCoordinateFourierL2
        hNS ht₀ hE hTail q j a b c d

  have hF4 : Continuous F4 := by
    dsimp only [F4]
    exact
      continuous_h3PreterminalSelectedVelocityFourthRadialFourierL2OnRestartRadius
        hNS ht₀ hE hTail j

  rw [continuous_iff_continuousAt]
  intro q₀
  apply tendsto_iff_norm_sub_tendsto_zero.2

  have hRad :
      Tendsto
        (fun q => ‖F4 q - F4 q₀‖)
        (𝓝 q₀)
        (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      hF4.continuousAt

  apply squeeze_zero
  · intro q
    exact norm_nonneg _
  · intro q
    dsimp only [C4, F4]
    exact
      norm_h3PreterminalSelectedVelocityFourthCoordinateFourierL2_sub_le
        hNS ht₀ hE hTail j a b c d q q₀
  · have hConst :
        Tendsto
          (fun _ :
            Set.Ioo
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
            (2 * Real.pi) ^ 4)
          (𝓝 q₀)
          (𝓝 ((2 * Real.pi) ^ 4)) :=
      tendsto_const_nhds

    have hMul :=
      hConst.mul hRad

    simpa only [mul_zero] using hMul

end

end Euclidean
end Bridge
end PrimeTensor
