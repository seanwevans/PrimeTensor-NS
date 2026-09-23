import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingRadialL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingPhysicalL2Jet

/-!
# Selected first forcing coordinate: strong Fourier L² continuity

The order-one temporal coefficient is the finite sum of repeated-index cubic
velocity terms minus one first spatial derivative of the selected Leray
forcing.  The cubic velocity side is now strongly continuous in physical L².

This file closes the corresponding Fourier L² continuity statement for the
forcing derivative.

The selected forcing already has strongly continuous radial Fourier L² states
on every positive terminal slab.  Since

    ‖D_a(ξ)‖ ≤ 2π ‖ξ‖,

the first coordinate multiplier is Lipschitz-dominated by the order-one radial
state.  Packaging the literal coordinate multiplier with `MemLp.toLp` and
applying this pointwise estimate to differences gives

    ‖F_a(s) - F_a(t)‖₂ ≤ 2π ‖F_rad,1(s) - F_rad,1(t)‖₂.

Hence radial order-one continuity immediately yields strong continuity of each
first coordinate forcing multiplier on the same slab.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedForcingFirstCoordinateFourierL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One selected first coordinate multiplier of the Leray forcing belongs to
Fourier `L²` at every positive restart time up to the restart radius. -/
theorem h3SelectedRestartForcingFirstCoordinate_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ)
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
          ((‖ξ‖ ^ 1 : ℝ) : ℂ) * N ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_radialWeight_memLp2
        1 hν U₀ hA hU₀ ht htR i

  have hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ * N ξ)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_derivative_integrable
        hν U₀ hA hU₀ ht htR i a

  refine
    hRadial.of_le_mul
      (c := 2 * Real.pi)
      hInt.aestronglyMeasurable
      ?_

  filter_upwards with ξ

  have hDeriv :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

  unfold h3FourierGradientMagnitude at hDeriv

  calc
    ‖h3FourierDerivativeSymbol a ξ * N ξ‖
        =
      ‖h3FourierDerivativeSymbol a ξ‖ * ‖N ξ‖ :=
      norm_mul _ _
    _ ≤
      ((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖ :=
      mul_le_mul_of_nonneg_right hDeriv (norm_nonneg _)
    _ =
      (2 * Real.pi) *
        ‖((‖ξ‖ ^ 1 : ℝ) : ℂ) * N ξ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp only [pow_one, abs_of_nonneg (norm_nonneg ξ)]
      ring

/-- Quotient-safe first coordinate forcing multiplier at one positive restart
time. -/
noncomputable def h3SelectedRestartForcingFirstCoordinateFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3) :
    H3FourierComplexL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  (h3SelectedRestartForcingFirstCoordinate_memLp2
      hν U₀ hA hU₀ ht htR i a).toLp
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol a ξ *
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i ξ)

/-- The packaged first coordinate multiplier has the literal Fourier amplitude
as its a.e. representative. -/
theorem h3SelectedRestartForcingFirstCoordinateFourierL2_ae
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3) :
    ((h3SelectedRestartForcingFirstCoordinateFourierL2
        hν U₀ hA hU₀ ht htR i a : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol a ξ *
        h3RawFinLerayOuterProductDivergence
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t)
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t)
          i ξ) := by
  unfold h3SelectedRestartForcingFirstCoordinateFourierL2
  exact
    MemLp.coeFn_toLp
      (h3SelectedRestartForcingFirstCoordinate_memLp2
        hν U₀ hA hU₀ ht htR i a)

/-- The first coordinate forcing multiplier, packaged on the same positive
terminal slab as the radial forcing states. -/
noncomputable def h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (s : Set.Icc (q / 2) q) :
    H3FourierComplexL2 :=
  h3SelectedRestartForcingFirstCoordinateFourierL2
    hν U₀ hA hU₀
    (by
      have hHalf : 0 < q / 2 := by positivity
      exact lt_of_lt_of_le hHalf s.property.1)
    (s.property.2.trans hqR)
    i a

/-- A.e. representative of the slab-packaged first coordinate forcing state. -/
theorem h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab_ae
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (s : Set.Icc (q / 2) q) :
    ((h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a s : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol a ξ *
        h3RawFinLerayOuterProductDivergence
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (s : ℝ))
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (s : ℝ))
          i ξ) := by
  unfold h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
  exact
    h3SelectedRestartForcingFirstCoordinateFourierL2_ae
      hν U₀ hA hU₀
      (by
        have hHalf : 0 < q / 2 := by positivity
        exact lt_of_lt_of_le hHalf s.property.1)
      (s.property.2.trans hqR)
      i a

/-- Coordinate-multiplier differences are controlled by the order-one radial
forcing difference with the sharp project symbol factor `2π`. -/
theorem norm_h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab_sub_le_radial
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (s t : Set.Icc (q / 2) q) :
    ‖h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
          hν U₀ hA hU₀ hq hqR i a s
        -
      h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
          hν U₀ hA hU₀ hq hqR i a t‖
      ≤
    (2 * Real.pi) *
      ‖h3SelectedRestartForcingRadialFourierL2OnSlab
          1 hν U₀ hA hU₀ hq hqR i s
        -
       h3SelectedRestartForcingRadialFourierL2OnSlab
          1 hν U₀ hA hU₀ hq hqR i t‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

  have hCoordSub :=
    MeasureTheory.Lp.coeFn_sub
      (h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a s)
      (h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a t)

  have hRadialSub :=
    MeasureTheory.Lp.coeFn_sub
      (h3SelectedRestartForcingRadialFourierL2OnSlab
        1 hν U₀ hA hU₀ hq hqR i s)
      (h3SelectedRestartForcingRadialFourierL2OnSlab
        1 hν U₀ hA hU₀ hq hqR i t)

  filter_upwards [
    hCoordSub,
    hRadialSub,
    h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab_ae
      hν U₀ hA hU₀ hq hqR i a s,
    h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab_ae
      hν U₀ hA hU₀ hq hqR i a t,
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      1 hν U₀ hA hU₀ hq hqR i s,
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      1 hν U₀ hA hU₀ hq hqR i t
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
    ‖h3FourierDerivativeSymbol a ξ * Ns -
        h3FourierDerivativeSymbol a ξ * Nt‖
      ≤
    (2 * Real.pi) *
      ‖((‖ξ‖ ^ 1 : ℝ) : ℂ) * Ns -
        ((‖ξ‖ ^ 1 : ℝ) : ℂ) * Nt‖

  rw [← mul_sub, ← mul_sub]
  rw [norm_mul, norm_mul]

  have hDeriv :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  unfold h3FourierGradientMagnitude at hDeriv

  have hRadialNorm :
      ‖((‖ξ‖ ^ 1 : ℝ) : ℂ)‖ = ‖ξ‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [pow_one, abs_of_nonneg (norm_nonneg ξ)]

  rw [hRadialNorm]

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ * ‖Ns - Nt‖
        ≤
      ((2 * Real.pi) * ‖ξ‖) * ‖Ns - Nt‖ :=
      mul_le_mul_of_nonneg_right hDeriv (norm_nonneg _)
    _ =
      (2 * Real.pi) * (‖ξ‖ * ‖Ns - Nt‖) := by
      ring

/-- Every first coordinate forcing multiplier is strongly continuous in
Fourier `L²` on every positive terminal slab. -/
theorem continuous_h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3) :
    Continuous
      (h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
        hν U₀ hA hU₀ hq hqR i a) := by
  let C : Set.Icc (q / 2) q → H3FourierComplexL2 :=
    h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
      hν U₀ hA hU₀ hq hqR i a

  let R : Set.Icc (q / 2) q → H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      1 hν U₀ hA hU₀ hq hqR i

  have hR : Continuous R := by
    dsimp only [R]
    exact
      continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
        1 hν U₀ hA hU₀ hq hqR i

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
        (fun _ : Set.Icc (q / 2) q => 2 * Real.pi)
        (𝓝 s₀)
        (𝓝 (2 * Real.pi)) :=
    tendsto_const_nhds

  have hScaled :
      Tendsto
        (fun s : Set.Icc (q / 2) q =>
          (2 * Real.pi) * ‖R s - R s₀‖)
        (𝓝 s₀)
        (𝓝 0) := by
    have hMul := hConst.mul hRadialTend
    simpa only [mul_zero] using hMul

  have hBound :
      ∀ s : Set.Icc (q / 2) q,
        ‖C s - C s₀‖ ≤
          (2 * Real.pi) * ‖R s - R s₀‖ := by
    intro s
    dsimp only [C, R]
    exact
      norm_h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab_sub_le_radial
        hν U₀ hA hU₀ hq hqR i a s s₀

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
