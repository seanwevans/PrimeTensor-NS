import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedCubicVelocityPhysicalL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedThirdVelocityL2Closure

/-!
# Identify the selected cubic physical L² package with the literal third jet

The preceding checkpoint transported the ordered cubic Fourier multiplier into
physical real `L²` and proved that this package is strongly continuous in time.

This file identifies that canonical package with the actual ordered third
spatial derivative of the selected real velocity.

There are two representation steps:

* inverse Plancherel agrees a.e. with the ordinary inverse Fourier integral
  whenever the cubic multiplier is integrable;
* the already-used one-coordinate inverse-Fourier derivative bridge is iterated
  three times, with the selected positive-time first/second/third moments
  supplying the required integrability.

Thus the continuous physical package is not merely an abstract reconstruction:
it is exactly the literal selected third spatial jet as an `H3ScalarL2` state.
Specializing the two inner axes to the same axis gives the repeated-index cubic
velocity path needed by the order-one temporal coefficient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform LineDeriv Topology
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedCubicVelocityPhysicalL2Identification
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderOneSelectedCubicVelocityPhysicalL2Identification :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- If the literal cubic coordinate multiplier is integrable, the canonical
physical package has the ordinary inverse Fourier real part as an a.e.
representative. -/
theorem h3SpectralScalarRawThirdCoordinatePhysicalL2_ae_eq_fourierInv
    (a b c : PrimeTensor.Axis Depth.three)
    (G : H3SpectralScalarState)
    (hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis a) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis b) ξ *
              (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ *
                h3SpectralScalarRawFourier G ξ)))
        (volume : Measure H3FourierPoint3)) :
    (((h3SpectralScalarRawThirdCoordinatePhysicalL2
          a b c G : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis a) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis b) ξ *
              (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ *
                h3SpectralScalarRawFourier G ξ)))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)) := by
  let third : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        (h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ *
            h3SpectralScalarRawFourier G ξ))

  let f2 : H3FourierComplexL2 :=
    h3SpectralScalarRawThirdCoordinateFourierL2 a b c G

  let u2 : H3FourierComplexL2 :=
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm f2

  let r2 : H3FourierRealL2 :=
    h3RealPartFourierL2 u2

  have hCompat :
      FourierTransformInv.fourierInv third
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2, third]
    unfold h3SpectralScalarRawThirdCoordinateFourierL2
    exact
      h3FourierInv_integrable_memLp2_ae_eq_L2
        hInt
        (h3SpectralScalarRawThirdCoordinate_memLp2 a b c G)

  have hCompatPoint :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv third
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hCompat

  have hRe :
      ((r2 : H3FourierRealL2) : H3FourierPoint3 → ℝ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ) ξ).re) := by
    dsimp only [r2]
    unfold h3RealPartFourierL2
    exact Complex.reCLM.coeFn_compLp u2

  have hRePoint :
      (fun x : Point3 =>
        ((r2 : H3FourierRealL2) : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hRe

  have hFrom :
      (((h3FromFourierRealL2 r2 : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((r2 : H3FourierRealL2) : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))) := by
    unfold h3FromFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        r2
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hAE :
      (((h3FromFourierRealL2 r2 : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv third
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)) := by
    filter_upwards [hFrom, hRePoint, hCompatPoint] with x hxFrom hxRe hxCompat
    calc
      ((h3FromFourierRealL2 r2 : H3ScalarL2) : Point3 → ℝ) x
          =
        ((r2 : H3FourierRealL2) : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x) := hxFrom
      _ =
        (((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := hxRe
      _ =
        (FourierTransformInv.fourierInv third
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re :=
        congrArg Complex.re hxCompat.symm

  simpa only [
    h3SpectralScalarRawThirdCoordinatePhysicalL2,
    r2, u2, f2, third
  ] using hAE

/-- At a strict positive selected restart time the literal cubic coordinate
multiplier is integrable. -/
theorem h3SelectedRestartRawThirdCoordinate_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis a) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis b) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis c) ξ *
              h3SpectralScalarRawFourier (W t i) ξ)))
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier (W t i)

  have hNInt :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 (W t i))

  have hNThirdMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 3 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ ht htR.le i

  have hDom :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 3 * (‖ξ‖ ^ 3 * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hNThirdMoment.const_mul ((2 * Real.pi) ^ 3)

  apply hDom.mono'

  · exact
      (h3FourierDerivativeSymbol_continuous
        (h3ClassicalizationFinOfAxis a)).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis b)).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous
            (h3ClassicalizationFinOfAxis c)).aestronglyMeasurable.mul
            hNInt.aestronglyMeasurable))

  · filter_upwards with ξ

    rw [norm_mul, norm_mul, norm_mul]

    have ha :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (h3ClassicalizationFinOfAxis a) ξ
    have hb :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (h3ClassicalizationFinOfAxis b) ξ
    have hc :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (h3ClassicalizationFinOfAxis c) ξ

    unfold h3FourierGradientMagnitude at ha hb hc

    calc
      ‖h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ‖ *
          (‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ‖ *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ‖ * ‖N ξ‖))
          ≤
        ((2 * Real.pi) * ‖ξ‖) *
          (‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ‖ *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ‖ * ‖N ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ ≤
        ((2 * Real.pi) * ‖ξ‖) *
          (((2 * Real.pi) * ‖ξ‖) *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ‖ * ‖N ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hb
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
            (by positivity)
      _ ≤
        ((2 * Real.pi) * ‖ξ‖) *
          (((2 * Real.pi) * ‖ξ‖) *
            (((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
              (by positivity))
            (by positivity)
      _ =
        (2 * Real.pi) ^ 3 * (‖ξ‖ ^ 3 * ‖N ξ‖) := by
        ring

/-- The literal selected third spatial derivative is exactly the ordinary
inverse Fourier reconstruction of its ordered cubic multiplier. -/
theorem h3SelectedRestartRealVelocity_spatial_d_three_eq_fourierInvThird
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (h3SpectralScalarRealC1RepresentativeOnPoint3 (W t i))))
      =
    (fun x : Point3 =>
      (FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis a) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis b) ξ *
              (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ *
                h3SpectralScalarRawFourier (W t i) ξ)))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier (W t i)

  let first : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis c) ξ * N ξ

  let second : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis b) ξ * first ξ

  let third : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ * second ξ

  have hNInt :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 (W t i))

  have hNFirstMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    simpa only [pow_one] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        1 hν U₀ hA hU₀ ht htR.le i

  have hNSecondMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 2 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        2 hν U₀ hA hU₀ ht htR.le i

  have hNThirdMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 3 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ ht htR.le i

  have hFirstInt :
      Integrable first (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) * (‖ξ‖ * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNFirstMoment.const_mul (2 * Real.pi)

    apply hDom.mono'
    · dsimp only [first]
      exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis c)).aestronglyMeasurable.mul
          hNInt.aestronglyMeasurable
    · filter_upwards with ξ
      dsimp only [first]
      rw [norm_mul]
      have hc :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ
      unfold h3FourierGradientMagnitude at hc
      calc
        ‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ‖ * ‖N ξ‖
            ≤ ((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ = (2 * Real.pi) * (‖ξ‖ * ‖N ξ‖) := by ring

  have hFirstMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖first ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) * (‖ξ‖ ^ 2 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNSecondMoment.const_mul (2 * Real.pi)

    apply hDom.mono'
    · exact
        continuous_norm.aestronglyMeasurable.mul
          hFirstInt.aestronglyMeasurable.norm
    · filter_upwards with ξ
      dsimp only [first]
      have hc :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ
      unfold h3FourierGradientMagnitude at hc
      have hLeft0 :
          0 ≤ ‖ξ‖ *
            ‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ * N ξ‖ := by positivity
      have hRight0 :
          0 ≤ (2 * Real.pi) * (‖ξ‖ ^ 2 * ‖N ξ‖) := by positivity
      have hBound :
          ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis c) ξ * N ξ‖
            ≤
          (2 * Real.pi) * (‖ξ‖ ^ 2 * ‖N ξ‖) := by
        rw [norm_mul]
        calc
          ‖ξ‖ *
              (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ‖ * ‖N ξ‖)
              ≤
            ‖ξ‖ * (((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
                (norm_nonneg ξ)
          _ = (2 * Real.pi) * (‖ξ‖ ^ 2 * ‖N ξ‖) := by ring
      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeft0,
        abs_of_nonneg hRight0
      ] using hBound

  have hSecondInt :
      Integrable second (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNSecondMoment.const_mul ((2 * Real.pi) ^ 2)

    apply hDom.mono'
    · dsimp only [second, first]
      exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis b)).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous
            (h3ClassicalizationFinOfAxis c)).aestronglyMeasurable.mul
            hNInt.aestronglyMeasurable)
    · filter_upwards with ξ
      dsimp only [second, first]
      rw [norm_mul, norm_mul]
      have hb :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis b) ξ
      have hc :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ
      unfold h3FourierGradientMagnitude at hb hc
      calc
        ‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ‖ *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ‖ * ‖N ξ‖)
            ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ‖ * ‖N ξ‖) := by
          exact
            mul_le_mul_of_nonneg_right
              hb (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
              (by positivity)
        _ = (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖N ξ‖) := by ring

  have hSecondMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖second ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 3 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNThirdMoment.const_mul ((2 * Real.pi) ^ 2)

    apply hDom.mono'
    · exact
        continuous_norm.aestronglyMeasurable.mul
          hSecondInt.aestronglyMeasurable.norm
    · filter_upwards with ξ
      dsimp only [second, first]
      have hb :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis b) ξ
      have hc :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ
      unfold h3FourierGradientMagnitude at hb hc
      have hLeft0 :
          0 ≤ ‖ξ‖ *
            ‖h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis b) ξ *
              (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis c) ξ * N ξ)‖ := by positivity
      have hRight0 :
          0 ≤ (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 3 * ‖N ξ‖) := by positivity
      have hBound :
          ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ * N ξ)‖
            ≤
          (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 3 * ‖N ξ‖) := by
        rw [norm_mul, norm_mul]
        calc
          ‖ξ‖ *
              (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ‖ *
                (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ‖ * ‖N ξ‖))
              ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ‖ * ‖N ξ‖)) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hb (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
                (norm_nonneg ξ)
          _ ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖)) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
                  (by positivity))
                (norm_nonneg ξ)
          _ = (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 3 * ‖N ξ‖) := by ring
      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeft0,
        abs_of_nonneg hRight0
      ] using hBound

  have hFirstEq :
      spatial3.d c
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv N
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv first
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    funext x
    dsimp only [first]
    exact
      fourierInv_re_onPoint3_spatialDerivative_eq_h3SelectedRawSecond
        hNInt hNFirstMoment c x

  have hSecondEq :
      spatial3.d b
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv first
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv second
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    funext x
    dsimp only [second]
    exact
      fourierInv_re_onPoint3_spatialDerivative_eq_h3SelectedRawSecond
        hFirstInt hFirstMoment b x

  have hThirdEq :
      spatial3.d a
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv second
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv third
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    funext x
    dsimp only [third]
    exact
      fourierInv_re_onPoint3_spatialDerivative_eq_h3SelectedRawSecond
        hSecondInt hSecondMoment a x

  have hBase :
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv N
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3 (W t i) := by
    rfl

  rw [← hBase]

  calc
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv N
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)))
        =
      spatial3.d a
        (spatial3.d b
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv first
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)) :=
      congrArg
        (fun f : ScalarField3 => spatial3.d a (spatial3.d b f))
        hFirstEq
    _ =
      spatial3.d a
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv second
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) :=
      congrArg (spatial3.d a) hSecondEq
    _ =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv third
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) :=
      hThirdEq

/-- At strict positive selected restart times, the continuous physical cubic
package is a.e. the literal ordered third spatial derivative. -/
theorem h3SelectedRestartRawThirdCoordinatePhysicalL2_ae_eq_spatial_d_three
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (((h3SpectralScalarRawThirdCoordinatePhysicalL2
          a b c (W t i) : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (h3SpectralScalarRealC1RepresentativeOnPoint3 (W t i))))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hInv :=
    h3SpectralScalarRawThirdCoordinatePhysicalL2_ae_eq_fourierInv
      a b c (W t i)
      (h3SelectedRestartRawThirdCoordinate_integrable
        hν U₀ hA hU₀ ht htR i a b c)

  have hPoint :=
    h3SelectedRestartRealVelocity_spatial_d_three_eq_fourierInvThird
      hν U₀ hA hU₀ ht htR i a b c

  filter_upwards [hInv] with x hx

  rw [hx]
  exact congrFun hPoint x |>.symm

/-- Canonical `H3ScalarL2` state carried by the literal ordered third selected
velocity derivative on the open restart interval. -/
noncomputable def h3SelectedRestartRealVelocityThirdCoordinateL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (q : Set.Ioo (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  (h3SelectedRestartRealVelocity_spatial_d_three_memLp2
      hν U₀ hA hU₀ q.property.1 q.property.2 i a b c).toLp
    (spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (h3SpectralScalarRealC1RepresentativeOnPoint3 (W q i)))))

/-- The literal selected third-jet `L²` state is exactly the continuous
physical reconstruction package. -/
theorem h3SelectedRestartRealVelocityThirdCoordinateL2_eq_rawPhysicalL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (q : Set.Ioo (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    h3SelectedRestartRealVelocityThirdCoordinateL2
        hν U₀ hA hU₀ q i a b c
      =
    h3SpectralScalarRawThirdCoordinatePhysicalL2
      a b c
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ q i) := by
  apply MeasureTheory.Lp.ext

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hLiteral :
      (((h3SelectedRestartRealVelocityThirdCoordinateL2
          hν U₀ hA hU₀ q i a b c : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (h3SpectralScalarRealC1RepresentativeOnPoint3 (W q i))))) := by
    dsimp only [h3SelectedRestartRealVelocityThirdCoordinateL2, W]
    exact
      MeasureTheory.MemLp.coeFn_toLp
        (h3SelectedRestartRealVelocity_spatial_d_three_memLp2
          hν U₀ hA hU₀ q.property.1 q.property.2 i a b c)

  have hPackage :=
    h3SelectedRestartRawThirdCoordinatePhysicalL2_ae_eq_spatial_d_three
      hν U₀ hA hU₀ q.property.1 q.property.2 i a b c

  filter_upwards [hLiteral, hPackage] with x hxLiteral hxPackage
  exact hxLiteral.trans hxPackage.symm

/-- Every literal ordered third selected velocity coordinate is strongly
continuous in physical `L²` on the open restart interval. -/
theorem continuous_h3SelectedRestartRealVelocityThirdCoordinateL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartRealVelocityThirdCoordinateL2
          hν U₀ hA hU₀ q i a b c) := by
  have hPhysical :
      Continuous
        (fun q : Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius ν A) =>
          h3SpectralScalarRawThirdCoordinatePhysicalL2
            a b c
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ (q : ℝ) i)) :=
    (continuous_h3SelectedRestartRawThirdCoordinatePhysicalL2
      hν U₀ hA hU₀ i a b c).comp
      continuous_subtype_val

  have hEq :
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartRealVelocityThirdCoordinateL2
          hν U₀ hA hU₀ q i a b c)
        =
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SpectralScalarRawThirdCoordinatePhysicalL2
          a b c
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (q : ℝ) i)) := by
    funext q
    exact
      h3SelectedRestartRealVelocityThirdCoordinateL2_eq_rawPhysicalL2
        hν U₀ hA hU₀ q i a b c

  rw [hEq]
  exact hPhysical

/-- Repeated-index specialization used by the order-one Laplacian term. -/
theorem continuous_h3SelectedRestartRealVelocityRepeatedThirdCoordinateL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (a k : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartRealVelocityThirdCoordinateL2
          hν U₀ hA hU₀ q i a k k) := by
  exact
    continuous_h3SelectedRestartRealVelocityThirdCoordinateL2
      hν U₀ hA hU₀ i a k k

end

end Euclidean
end Bridge
end PrimeTensor
