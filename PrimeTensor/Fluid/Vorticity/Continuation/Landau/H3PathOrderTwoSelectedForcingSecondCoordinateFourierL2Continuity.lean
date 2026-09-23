import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingRadialL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingPhysicalL2Jet

/-!
# Selected second forcing coordinate: strong Fourier L² continuity

The order-two temporal coefficient contains the selected forcing Hessian

    ∂ₐ∂ᵦ Nⱼ(S,S).

The selected forcing already has strongly continuous radial Fourier `L²` states
at every finite radial order on each positive terminal slab.  At order two,

    ‖Dₐ(ξ) Dᵦ(ξ)‖ ≤ (2π)² ‖ξ‖²,

so the ordered second coordinate multiplier is Lipschitz-dominated by the
order-two radial state.

This file makes the second-coordinate `MemLp` estimate public, packages the
literal coordinate multiplier as a quotient-safe Fourier `L²` state, proves
the difference estimate, and closes strong Fourier `L²` continuity on each
positive slab.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedForcingSecondCoordinateFourierL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Public order-two coordinate-multiplier `L²` estimate for the selected
Leray forcing. -/
theorem h3SelectedRestartForcingSecondCoordinate_memLp2
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
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ))
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
          ((‖ξ‖ ^ 2 : ℝ) : ℂ) * N ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_radialWeight_memLp2
        2 hν U₀ hA hU₀ ht htR i

  have hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ * N ξ))
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondCoordinate_integrable
        hν U₀ hA hU₀ ht htR i a b

  refine
    hRadial.of_le_mul
      (c := (2 * Real.pi) ^ 2)
      hInt.aestronglyMeasurable
      ?_

  filter_upwards with ξ

  rw [norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ

  have hGrad0 :
      0 ≤ h3FourierGradientMagnitude ξ := by
    unfold h3FourierGradientMagnitude
    positivity

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ * ‖N ξ‖)
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol b ξ‖ * ‖N ξ‖) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ * ‖N ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
          hGrad0
    _ =
      (2 * Real.pi) ^ 2 *
        ‖((‖ξ‖ ^ 2 : ℝ) : ℂ) * N ξ‖ := by
      unfold h3FourierGradientMagnitude
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 2)]
      ring

/-- Quotient-safe selected forcing second-coordinate multiplier at one positive
restart time. -/
noncomputable def h3SelectedRestartForcingSecondCoordinateFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3) :
    H3FourierComplexL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  (h3SelectedRestartForcingSecondCoordinate_memLp2
      hν U₀ hA hU₀ ht htR i a b).toLp
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ))

/-- The packaged second coordinate multiplier has the literal amplitude as its
a.e. representative. -/
theorem h3SelectedRestartForcingSecondCoordinateFourierL2_ae
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3) :
    ((h3SelectedRestartForcingSecondCoordinateFourierL2
        hν U₀ hA hU₀ ht htR i a b : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          h3RawFinLerayOuterProductDivergence
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t)
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t)
            i ξ)) := by
  unfold h3SelectedRestartForcingSecondCoordinateFourierL2
  exact
    MemLp.coeFn_toLp
      (h3SelectedRestartForcingSecondCoordinate_memLp2
        hν U₀ hA hU₀ ht htR i a b)

/-- The second coordinate forcing multiplier on a positive terminal slab. -/
noncomputable def h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (s : Set.Icc (q / 2) q) :
    H3FourierComplexL2 :=
  h3SelectedRestartForcingSecondCoordinateFourierL2
    hν U₀ hA hU₀
    (by
      have hHalf : 0 < q / 2 := by positivity
      exact lt_of_lt_of_le hHalf s.property.1)
    (s.property.2.trans hqR)
    i a b

/-- A.e. representative of the slab-packaged second coordinate forcing
state. -/
theorem h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab_ae
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (s : Set.Icc (q / 2) q) :
    ((h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b s : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          h3RawFinLerayOuterProductDivergence
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ (s : ℝ))
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ (s : ℝ))
            i ξ)) := by
  unfold h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
  exact
    h3SelectedRestartForcingSecondCoordinateFourierL2_ae
      hν U₀ hA hU₀
      (by
        have hHalf : 0 < q / 2 := by positivity
        exact lt_of_lt_of_le hHalf s.property.1)
      (s.property.2.trans hqR)
      i a b

/-- Ordered second-coordinate multiplier differences are controlled by the
order-two radial forcing difference. -/
theorem norm_h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab_sub_le_radial
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (s t : Set.Icc (q / 2) q) :
    ‖h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
          hν U₀ hA hU₀ hq hqR i a b s
        -
      h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
          hν U₀ hA hU₀ hq hqR i a b t‖
      ≤
    (2 * Real.pi) ^ 2 *
      ‖h3SelectedRestartForcingRadialFourierL2OnSlab
          2 hν U₀ hA hU₀ hq hqR i s
        -
       h3SelectedRestartForcingRadialFourierL2OnSlab
          2 hν U₀ hA hU₀ hq hqR i t‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

  have hCoordSub :=
    MeasureTheory.Lp.coeFn_sub
      (h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b s)
      (h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b t)

  have hRadialSub :=
    MeasureTheory.Lp.coeFn_sub
      (h3SelectedRestartForcingRadialFourierL2OnSlab
        2 hν U₀ hA hU₀ hq hqR i s)
      (h3SelectedRestartForcingRadialFourierL2OnSlab
        2 hν U₀ hA hU₀ hq hqR i t)

  filter_upwards [
    hCoordSub,
    hRadialSub,
    h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab_ae
      hν U₀ hA hU₀ hq hqR i a b s,
    h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab_ae
      hν U₀ hA hU₀ hq hqR i a b t,
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      2 hν U₀ hA hU₀ hq hqR i s,
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      2 hν U₀ hA hU₀ hq hqR i t
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
        (h3FourierDerivativeSymbol b ξ * Ns) -
      h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ * Nt)‖
      ≤
    (2 * Real.pi) ^ 2 *
      ‖((‖ξ‖ ^ 2 : ℝ) : ℂ) * Ns -
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) * Nt‖

  rw [← mul_sub, ← mul_sub, ← mul_sub]
  rw [norm_mul, norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ

  unfold h3FourierGradientMagnitude at ha hb

  have hRadialNorm :
      ‖((‖ξ‖ ^ 2 : ℝ) : ℂ)‖ = ‖ξ‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 2)

  rw [hRadialNorm]

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ * ‖Ns - Nt‖)
        ≤
      ((2 * Real.pi) * ‖ξ‖) *
        (‖h3FourierDerivativeSymbol b ξ‖ * ‖Ns - Nt‖) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤
      ((2 * Real.pi) * ‖ξ‖) *
        (((2 * Real.pi) * ‖ξ‖) * ‖Ns - Nt‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
          (by positivity)
    _ =
      (2 * Real.pi) ^ 2 *
        (‖ξ‖ ^ 2 * ‖Ns - Nt‖) := by
      ring

/-- Every ordered second coordinate forcing multiplier is strongly continuous
in Fourier `L²` on every positive terminal slab. -/
theorem continuous_h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3) :
    Continuous
      (h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b) := by
  let C : Set.Icc (q / 2) q → H3FourierComplexL2 :=
    h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
      hν U₀ hA hU₀ hq hqR i a b

  let R : Set.Icc (q / 2) q → H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      2 hν U₀ hA hU₀ hq hqR i

  have hR : Continuous R := by
    dsimp only [R]
    exact
      continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
        2 hν U₀ hA hU₀ hq hqR i

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
        (fun _ : Set.Icc (q / 2) q => (2 * Real.pi) ^ 2)
        (𝓝 s₀)
        (𝓝 ((2 * Real.pi) ^ 2)) :=
    tendsto_const_nhds

  have hScaled :
      Tendsto
        (fun s : Set.Icc (q / 2) q =>
          (2 * Real.pi) ^ 2 * ‖R s - R s₀‖)
        (𝓝 s₀)
        (𝓝 0) := by
    have hMul := hConst.mul hRadialTend
    simpa only [mul_zero] using hMul

  have hBound :
      ∀ s : Set.Icc (q / 2) q,
        ‖C s - C s₀‖
          ≤
        (2 * Real.pi) ^ 2 * ‖R s - R s₀‖ := by
    intro s
    dsimp only [C, R]
    exact
      norm_h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab_sub_le_radial
        hν U₀ hA hU₀ hq hqR i a b s s₀

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
