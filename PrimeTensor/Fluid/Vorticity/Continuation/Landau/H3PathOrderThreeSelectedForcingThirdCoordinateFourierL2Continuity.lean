import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingRadialL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingPhysicalL2Jet

/-!
# Selected third forcing coordinate: strong Fourier L² continuity

The order-three temporal coefficient contains the selected forcing third
derivative

    ∂ₐ∂ᵦ∂𝑐 Nⱼ(S,S).

The selected Leray forcing already has strongly continuous radial Fourier `L²`
states at every finite radial order on each positive terminal slab.  At order
three,

    ‖Dₐ(ξ) Dᵦ(ξ) D𝑐(ξ)‖ ≤ (2π)³ ‖ξ‖³,

so the ordered third-coordinate multiplier is Lipschitz-dominated by the
order-three radial forcing state.

This file packages that multiplier as a quotient-safe Fourier `L²` state,
proves the radial difference estimate, and closes strong Fourier `L²`
continuity on every positive terminal slab.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedForcingThirdCoordinateFourierL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Public order-three coordinate-multiplier `L²` estimate for the selected
Leray forcing. -/
theorem h3SelectedRestartForcingThirdCoordinate_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ *
              h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ)))
      2
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  have hRadial :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 3 : ℝ) : ℂ) * N ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_radialWeight_memLp2
        3 hν U₀ hA hU₀ ht htR i

  have hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ *
              (h3FourierDerivativeSymbol c ξ * N ξ)))
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdCoordinate_integrable
        hν U₀ hA hU₀ ht htR i a b c

  refine
    hRadial.of_le_mul
      (c := (2 * Real.pi) ^ 3)
      hInt.aestronglyMeasurable
      ?_

  filter_upwards with ξ

  rw [norm_mul, norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ
  have hc :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude c ξ

  have hGrad0 :
      0 ≤ h3FourierGradientMagnitude ξ := by
    unfold h3FourierGradientMagnitude
    positivity

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ * ‖N ξ‖))
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ * ‖N ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol c ξ‖ * ‖N ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hb
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          hGrad0
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ * ‖N ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
            hGrad0)
          hGrad0
    _ =
      (2 * Real.pi) ^ 3 *
        ‖((‖ξ‖ ^ 3 : ℝ) : ℂ) * N ξ‖ := by
      unfold h3FourierGradientMagnitude
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 3)]
      ring

/-- Quotient-safe selected forcing third-coordinate multiplier at one positive
restart time. -/
noncomputable def h3SelectedRestartForcingThirdCoordinateFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3) :
    H3FourierComplexL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  (h3SelectedRestartForcingThirdCoordinate_memLp2
      hν U₀ hA hU₀ ht htR i a b c).toLp
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          (h3FourierDerivativeSymbol c ξ *
            h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ)))

/-- The packaged third-coordinate multiplier has the literal amplitude as its
a.e. representative. -/
theorem h3SelectedRestartForcingThirdCoordinateFourierL2_ae
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3) :
    ((h3SelectedRestartForcingThirdCoordinateFourierL2
        hν U₀ hA hU₀ ht htR i a b c : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          (h3FourierDerivativeSymbol c ξ *
            h3RawFinLerayOuterProductDivergence
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t)
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t)
              i ξ))) := by
  unfold h3SelectedRestartForcingThirdCoordinateFourierL2
  exact
    MemLp.coeFn_toLp
      (h3SelectedRestartForcingThirdCoordinate_memLp2
        hν U₀ hA hU₀ ht htR i a b c)

/-- The third-coordinate forcing multiplier on a positive terminal slab. -/
noncomputable def h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (s : Set.Icc (q / 2) q) :
    H3FourierComplexL2 :=
  h3SelectedRestartForcingThirdCoordinateFourierL2
    hν U₀ hA hU₀
    (by
      have hHalf : 0 < q / 2 := by positivity
      exact lt_of_lt_of_le hHalf s.property.1)
    (s.property.2.trans hqR)
    i a b c

/-- A.e. representative of the slab-packaged third-coordinate forcing state. -/
theorem h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab_ae
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (s : Set.Icc (q / 2) q) :
    ((h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b c s : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          (h3FourierDerivativeSymbol c ξ *
            h3RawFinLerayOuterProductDivergence
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ (s : ℝ))
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ (s : ℝ))
              i ξ))) := by
  unfold h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
  exact
    h3SelectedRestartForcingThirdCoordinateFourierL2_ae
      hν U₀ hA hU₀
      (by
        have hHalf : 0 < q / 2 := by positivity
        exact lt_of_lt_of_le hHalf s.property.1)
      (s.property.2.trans hqR)
      i a b c

/-- Ordered third-coordinate multiplier differences are controlled by the
order-three radial forcing difference. -/
theorem norm_h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab_sub_le_radial
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (s t : Set.Icc (q / 2) q) :
    ‖h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
          hν U₀ hA hU₀ hq hqR i a b c s
        -
      h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
          hν U₀ hA hU₀ hq hqR i a b c t‖
      ≤
    (2 * Real.pi) ^ 3 *
      ‖h3SelectedRestartForcingRadialFourierL2OnSlab
          3 hν U₀ hA hU₀ hq hqR i s
        -
       h3SelectedRestartForcingRadialFourierL2OnSlab
          3 hν U₀ hA hU₀ hq hqR i t‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

  have hCoordSub :=
    MeasureTheory.Lp.coeFn_sub
      (h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b c s)
      (h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b c t)

  have hRadialSub :=
    MeasureTheory.Lp.coeFn_sub
      (h3SelectedRestartForcingRadialFourierL2OnSlab
        3 hν U₀ hA hU₀ hq hqR i s)
      (h3SelectedRestartForcingRadialFourierL2OnSlab
        3 hν U₀ hA hU₀ hq hqR i t)

  filter_upwards [
    hCoordSub,
    hRadialSub,
    h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab_ae
      hν U₀ hA hU₀ hq hqR i a b c s,
    h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab_ae
      hν U₀ hA hU₀ hq hqR i a b c t,
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      3 hν U₀ hA hU₀ hq hqR i s,
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      3 hν U₀ hA hU₀ hq hqR i t
  ] with ξ hCoordSubξ hRadialSubξ hs ht hrs hrt

  rw [hCoordSubξ, hRadialSubξ]
  simp only [Pi.sub_apply]
  rw [hs, ht, hrs, hrt]

  let Ns : ℂ :=
    h3RawFinLerayOuterProductDivergence
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ (s : ℝ))
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ (s : ℝ))
      i ξ

  let Nt : ℂ :=
    h3RawFinLerayOuterProductDivergence
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ (t : ℝ))
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ (t : ℝ))
      i ξ

  change
    ‖h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          (h3FourierDerivativeSymbol c ξ * Ns)) -
      h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          (h3FourierDerivativeSymbol c ξ * Nt))‖
      ≤
    (2 * Real.pi) ^ 3 *
      ‖((‖ξ‖ ^ 3 : ℝ) : ℂ) * Ns -
        ((‖ξ‖ ^ 3 : ℝ) : ℂ) * Nt‖

  rw [← mul_sub, ← mul_sub, ← mul_sub, ← mul_sub]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ
  have hc :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude c ξ

  unfold h3FourierGradientMagnitude at ha hb hc

  have hRadialNorm :
      ‖((‖ξ‖ ^ 3 : ℝ) : ℂ)‖ = ‖ξ‖ ^ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 3)

  rw [hRadialNorm]

  have hpi0 : 0 ≤ 2 * Real.pi := by
    positivity

  have hr0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ * ‖Ns - Nt‖))
        ≤
      ((2 * Real.pi) * ‖ξ‖) *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ * ‖Ns - Nt‖)) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ ≤
      ((2 * Real.pi) * ‖ξ‖) *
        (((2 * Real.pi) * ‖ξ‖) *
          (‖h3FourierDerivativeSymbol c ξ‖ * ‖Ns - Nt‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hb
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          (mul_nonneg hpi0 hr0)
    _ ≤
      ((2 * Real.pi) * ‖ξ‖) *
        (((2 * Real.pi) * ‖ξ‖) *
          (((2 * Real.pi) * ‖ξ‖) * ‖Ns - Nt‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
            (mul_nonneg hpi0 hr0))
          (mul_nonneg hpi0 hr0)
    _ =
      (2 * Real.pi) ^ 3 *
        (‖ξ‖ ^ 3 * ‖Ns - Nt‖) := by
      ring

/-- Every ordered third-coordinate forcing multiplier is strongly continuous
in Fourier `L²` on every positive terminal slab. -/
theorem continuous_h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3) :
    Continuous
      (h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b c) := by

  let C : Set.Icc (q / 2) q → H3FourierComplexL2 :=
    h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
      hν U₀ hA hU₀ hq hqR i a b c

  let R : Set.Icc (q / 2) q → H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      3 hν U₀ hA hU₀ hq hqR i

  have hR : Continuous R := by
    dsimp only [R]
    exact
      continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
        3 hν U₀ hA hU₀ hq hqR i

  rw [continuous_iff_continuousAt]
  intro s₀

  apply tendsto_iff_norm_sub_tendsto_zero.2

  have hRadialTend :
      Tendsto
        (fun s : Set.Icc (q / 2) q => ‖R s - R s₀‖)
        (𝓝 s₀)
        (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hR.continuousAt

  have hConst :
      Tendsto
        (fun _ : Set.Icc (q / 2) q => (2 * Real.pi) ^ 3)
        (𝓝 s₀)
        (𝓝 ((2 * Real.pi) ^ 3)) :=
    tendsto_const_nhds

  have hScaled :
      Tendsto
        (fun s : Set.Icc (q / 2) q =>
          (2 * Real.pi) ^ 3 * ‖R s - R s₀‖)
        (𝓝 s₀)
        (𝓝 0) := by
    have hMul := hConst.mul hRadialTend
    simpa only [mul_zero] using hMul

  have hBound :
      ∀ s : Set.Icc (q / 2) q,
        ‖C s - C s₀‖
          ≤
        (2 * Real.pi) ^ 3 * ‖R s - R s₀‖ := by
    intro s
    dsimp only [C, R]
    exact
      norm_h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab_sub_le_radial
        hν U₀ hA hU₀ hq hqR i a b c s s₀

  have hTarget :
      Tendsto
        (fun s : Set.Icc (q / 2) q => ‖C s - C s₀‖)
        (𝓝 s₀)
        (𝓝 0) :=
    squeeze_zero
      (fun s => norm_nonneg (C s - C s₀))
      hBound
      hScaled

  simpa only [C] using hTarget

end

end Euclidean
end Bridge
end PrimeTensor
