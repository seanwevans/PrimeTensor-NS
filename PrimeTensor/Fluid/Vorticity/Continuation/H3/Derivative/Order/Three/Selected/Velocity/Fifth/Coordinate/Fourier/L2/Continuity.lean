import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Three.Selected.Velocity.Fifth.Radial.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path

/-!
# Selected fifth-coordinate velocity Fourier L² continuity

The selected fifth-radial Fourier `L²` state is now strongly continuous on the
strict restart interval.

Every ordered fifth spatial coordinate multiplier is pointwise dominated by
the fifth-radial multiplier:

    |mₐ mᵦ m𝑐 m𝑑 mₑ z|
      ≤ (2π)⁵ |ξ|⁵ |z|.

This file packages each ordered fifth coordinate as quotient-safe Fourier
`L²`, identifies the elementary five-symbol product with the repository's
native selected fifth Fréchet raw coordinate multiplier, and transfers
fifth-radial strong continuity to every ordered fifth coordinate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedVelocityFifthCoordinateFourierL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

private noncomputable def h3OrderThreeFifthCoordinateMultiplier
    (a b c d e : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3)
    (z : ℂ) : ℂ :=
  h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ *
    (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ *
      (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis c) ξ *
        (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis d) ξ *
          (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis e) ξ * z))))

private theorem h3OrderThreeFifthCoordinateMultiplier_sub
    (a b c d e : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3)
    (z w : ℂ) :
    h3OrderThreeFifthCoordinateMultiplier a b c d e ξ (z - w)
      =
    h3OrderThreeFifthCoordinateMultiplier a b c d e ξ z
      -
    h3OrderThreeFifthCoordinateMultiplier a b c d e ξ w := by
  unfold h3OrderThreeFifthCoordinateMultiplier
  ring

private theorem norm_h3OrderThreeFifthCoordinateMultiplier_le_radial
    (a b c d e : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3)
    (z : ℂ) :
    ‖h3OrderThreeFifthCoordinateMultiplier a b c d e ξ z‖
      ≤
    (2 * Real.pi) ^ 5 *
      ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * z‖ := by
  unfold h3OrderThreeFifthCoordinateMultiplier
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]

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
  have he :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude
      (h3ClassicalizationFinOfAxis e) ξ

  have hGrad0 : 0 ≤ h3FourierGradientMagnitude ξ := by
    unfold h3FourierGradientMagnitude
    positivity

  calc
    ‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ‖ *
        (‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ‖ *
          (‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis c) ξ‖ *
            (‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis d) ξ‖ *
              (‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis e) ξ‖ * ‖z‖))))
        ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (h3FourierGradientMagnitude ξ *
              (h3FourierGradientMagnitude ξ * ‖z‖)))) := by
      gcongr
    _ =
      (2 * Real.pi) ^ 5 *
        ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * z‖ := by
      unfold h3FourierGradientMagnitude
      rw [
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 5)
      ]
      ring

/-- The elementary ordered five-symbol product is exactly the repository's
native selected fifth Fréchet raw coordinate multiplier. -/
private theorem h3OrderThreeFifthCoordinateMultiplier_eq_selectedFrechet
    (H : H3SpectralScalarState)
    (a b c d e : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3) :
    h3OrderThreeFifthCoordinateMultiplier a b c d e ξ
        (h3SpectralScalarRawFourier H ξ)
      =
    h3SelectedFifthFrechetRawCoordinateMultiplier
      H a b c d e ξ := by

  let ea : H3FourierPoint3 := h3FourierAxisDirection a
  let eb : H3FourierPoint3 := h3FourierAxisDirection b
  let ec : H3FourierPoint3 := h3FourierAxisDirection c
  let ed : H3FourierPoint3 := h3FourierAxisDirection d
  let ee : H3FourierPoint3 := h3FourierAxisDirection e

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

  have he :
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis e) ξ
        =
      ((2 * Real.pi * inner ℝ ξ ee : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ee]
    rw [h3FourierDerivativeSymbol_eq_inner]
    rw [h3AxisOfFin3_h3ClassicalizationFinOfAxis]
    push_cast
    ring

  unfold h3OrderThreeFifthCoordinateMultiplier
  unfold h3SelectedFifthFrechetRawCoordinateMultiplier
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

  rw [ha, hb, hc, hd, he]
  dsimp only [ea, eb, ec, ed, ee]
  simp [Complex.real_smul] <;> push_cast <;> ring

theorem h3PreterminalSelectedVelocityFifthCoordinate_memLp2
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
    (a b c d e : PrimeTensor.Axis Depth.three) :
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
        h3OrderThreeFifthCoordinateMultiplier a b c d e ξ
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
    hM.2 a b c d e j

  have hAE :
      (fun ξ : H3FourierPoint3 =>
        h3OrderThreeFifthCoordinateMultiplier a b c d e ξ
          (h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              (q : ℝ) j) ξ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SelectedFifthFrechetRawCoordinateMultiplier
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          (q : ℝ) j)
        a b c d e := by
    filter_upwards with ξ
    exact
      h3OrderThreeFifthCoordinateMultiplier_eq_selectedFrechet
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          (q : ℝ) j)
        a b c d e ξ

  exact
    (memLp_congr_ae hAE).2 hNative

noncomputable def h3PreterminalSelectedVelocityFifthCoordinateFourierL2
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
    (a b c d e : PrimeTensor.Axis Depth.three) :
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
  (h3PreterminalSelectedVelocityFifthCoordinate_memLp2
      hNS ht₀ hE hTail q j a b c d e).toLp
    (fun ξ : H3FourierPoint3 =>
      h3OrderThreeFifthCoordinateMultiplier a b c d e ξ
        (h3SpectralScalarRawFourier (W (q : ℝ) j) ξ))

theorem h3PreterminalSelectedVelocityFifthCoordinateFourierL2_ae
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
    (a b c d e : PrimeTensor.Axis Depth.three) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
    ((h3PreterminalSelectedVelocityFifthCoordinateFourierL2
        hNS ht₀ hE hTail q j a b c d e :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3OrderThreeFifthCoordinateMultiplier a b c d e ξ
        (h3SpectralScalarRawFourier (W (q : ℝ) j) ξ)) := by
  dsimp only
  unfold h3PreterminalSelectedVelocityFifthCoordinateFourierL2
  exact
    MemLp.coeFn_toLp
      (h3PreterminalSelectedVelocityFifthCoordinate_memLp2
        hNS ht₀ hE hTail q j a b c d e)

theorem norm_h3PreterminalSelectedVelocityFifthCoordinateFourierL2_sub_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3)
    (a b c d e : PrimeTensor.Axis Depth.three)
    (s t : Set.Ioo
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    ‖h3PreterminalSelectedVelocityFifthCoordinateFourierL2
          hNS ht₀ hE hTail s j a b c d e
        -
      h3PreterminalSelectedVelocityFifthCoordinateFourierL2
          hNS ht₀ hE hTail t j a b c d e‖
      ≤
    (2 * Real.pi) ^ 5 *
      ‖h3PreterminalSelectedVelocityFifthRadialFourierL2
          hNS ht₀ hE hTail s j
        -
        h3PreterminalSelectedVelocityFifthRadialFourierL2
          hNS ht₀ hE hTail t j‖ := by

  let Cs : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthCoordinateFourierL2
      hNS ht₀ hE hTail s j a b c d e
  let Ct : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthCoordinateFourierL2
      hNS ht₀ hE hTail t j a b c d e
  let Rs : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2
      hNS ht₀ hE hTail s j
  let Rt : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2
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
    h3PreterminalSelectedVelocityFifthCoordinateFourierL2_ae
      hNS ht₀ hE hTail s j a b c d e
  have hCt :=
    h3PreterminalSelectedVelocityFifthCoordinateFourierL2_ae
      hNS ht₀ hE hTail t j a b c d e
  have hRs :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2_ae
      hNS ht₀ hE hTail s j
  have hRt :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2_ae
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
  unfold h3SelectedRawFourierFifthRadialWeight
  rw [← h3OrderThreeFifthCoordinateMultiplier_sub]
  rw [← mul_sub]

  exact
    norm_h3OrderThreeFifthCoordinateMultiplier_le_radial
      a b c d e ξ
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

theorem continuous_h3PreterminalSelectedVelocityFifthCoordinateFourierL2OnRestartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3)
    (a b c d e : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q : Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedVelocityFifthCoordinateFourierL2
          hNS ht₀ hE hTail q j a b c d e) := by

  let F5 :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        H3FourierComplexL2 :=
    fun q =>
      h3PreterminalSelectedVelocityFifthRadialFourierL2
        hNS ht₀ hE hTail q j

  let C5 :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        H3FourierComplexL2 :=
    fun q =>
      h3PreterminalSelectedVelocityFifthCoordinateFourierL2
        hNS ht₀ hE hTail q j a b c d e

  have hF5 : Continuous F5 := by
    dsimp only [F5]
    exact
      continuous_h3PreterminalSelectedVelocityFifthRadialFourierL2OnRestartRadius
        hNS ht₀ hE hTail j

  rw [continuous_iff_continuousAt]
  intro q₀
  apply tendsto_iff_norm_sub_tendsto_zero.2

  have hRad :
      Tendsto
        (fun q => ‖F5 q - F5 q₀‖)
        (𝓝 q₀)
        (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      hF5.continuousAt

  apply squeeze_zero
  · intro q
    exact norm_nonneg _
  · intro q
    dsimp only [C5, F5]
    exact
      norm_h3PreterminalSelectedVelocityFifthCoordinateFourierL2_sub_le
        hNS ht₀ hE hTail j a b c d e q q₀
  · have hConst :
        Tendsto
          (fun _ :
            Set.Ioo
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
            (2 * Real.pi) ^ 5)
          (𝓝 q₀)
          (𝓝 ((2 * Real.pi) ^ 5)) :=
      tendsto_const_nhds

    have hMul :=
      hConst.mul hRad

    simpa only [mul_zero] using hMul

end

end Euclidean
end Bridge
end PrimeTensor
