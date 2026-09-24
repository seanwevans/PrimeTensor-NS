import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderTwoSelectedVelocityFourthCoordinatePhysicalL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedCubicVelocityPhysicalL2Identification
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathClosedArbitraryFourthVelocityJets

/-!
# Identify the continuous selected fourth-coordinate physical L² package

The preceding checkpoint transported every ordered fourth selected Fourier
coordinate continuously into physical real `L²`.

This file identifies that continuous package with the literal ordered fourth
spatial derivative of the selected real velocity.

Rather than repeat the complete inverse-Fourier derivative induction, we reuse
the already-closed cubic identification.  For

    third(ξ) = d_b(ξ) d_c(ξ) d_d(ξ) N(ξ),

the cubic theorem identifies `D_b D_c D_d u` with `fourierInv third`.  The
fourth raw moment gives

    ξ ↦ |ξ| |third(ξ)|

in `L¹`, so one final application of the project's inverse-Fourier derivative
bridge produces the `a` derivative.  This yields the exact ordered fourth
coordinate.

The final result is a literal fourth-jet `H3ScalarL2` path which is strongly
continuous on the strict restart interval.  The repeated `(a,b,k,k)`
specialization is exactly the diffusion input for the order-two temporal
coefficient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform LineDeriv Topology
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedVelocityFourthCoordinatePhysicalL2Identification
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderTwoSelectedVelocityFourthCoordinatePhysicalL2Identification :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## One more derivative beyond the cubic bridge -/

/-- At strict positive selected restart times the literal ordered fourth
coordinate Fourier multiplier is integrable. -/
theorem h3SelectedRestartRawFourthCoordinate_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three) :
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
              (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis d) ξ *
                h3SpectralScalarRawFourier (W t i) ξ))))
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier (W t i)

  let third : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis b) ξ *
        (h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis d) ξ *
            N ξ))

  let fourth : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        third ξ

  have hThirdInt :
      Integrable third
        (volume : Measure H3FourierPoint3) := by
    dsimp only [third, N, W]
    exact
      h3SelectedRestartRawThirdCoordinate_integrable
        hν U₀ hA hU₀ ht htR i b c d

  have hNFourthMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        4 hν U₀ hA hU₀ ht htR.le i

  have hThirdMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖third ξ‖)
        (volume : Measure H3FourierPoint3) := by

    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 3 *
              (‖ξ‖ ^ 4 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNFourthMoment.const_mul ((2 * Real.pi) ^ 3)

    apply hDom.mono'

    · exact
        continuous_norm.aestronglyMeasurable.mul
          hThirdInt.aestronglyMeasurable.norm

    · filter_upwards with ξ

      dsimp only [third]

      have hb :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis b) ξ
      have hc :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ
      have hd :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis d) ξ

      unfold h3FourierGradientMagnitude at hb hc hd

      have hLeft0 :
          0 ≤
            ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ *
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ *
                    N ξ))‖ := by
        positivity

      have hRight0 :
          0 ≤
            (2 * Real.pi) ^ 3 *
              (‖ξ‖ ^ 4 * ‖N ξ‖) := by
        positivity

      have hBound :
          ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ *
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ *
                    N ξ))‖
            ≤
          (2 * Real.pi) ^ 3 *
            (‖ξ‖ ^ 4 * ‖N ξ‖) := by

        rw [norm_mul, norm_mul, norm_mul]

        calc
          ‖ξ‖ *
              (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ‖ *
                (‖h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ‖ *
                  (‖h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ‖ *
                    ‖N ξ‖)))
              ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (‖h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ‖ *
                  (‖h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ‖ *
                    ‖N ξ‖))) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hb
                  (mul_nonneg
                    (norm_nonneg _)
                    (mul_nonneg
                      (norm_nonneg _)
                      (norm_nonneg _))))
                (norm_nonneg ξ)
          _ ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (((2 * Real.pi) * ‖ξ‖) *
                  (‖h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ‖ *
                    ‖N ξ‖))) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right
                    hc
                    (mul_nonneg
                      (norm_nonneg _)
                      (norm_nonneg _)))
                  (by positivity))
                (norm_nonneg ξ)
          _ ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (((2 * Real.pi) * ‖ξ‖) *
                  (((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖))) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right
                      hd
                      (norm_nonneg _))
                    (by positivity))
                  (by positivity))
                (norm_nonneg ξ)
          _ =
            (2 * Real.pi) ^ 3 *
              (‖ξ‖ ^ 4 * ‖N ξ‖) := by
            ring

      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeft0,
        abs_of_nonneg hRight0
      ] using hBound

  have hFourthInt :
      Integrable fourth
        (volume : Measure H3FourierPoint3) := by

    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) *
              (‖ξ‖ * ‖third ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hThirdMoment.const_mul (2 * Real.pi)

    apply hDom.mono'

    · dsimp only [fourth]
      exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis a)).aestronglyMeasurable.mul
          hThirdInt.aestronglyMeasurable

    · filter_upwards with ξ
      dsimp only [fourth]
      rw [norm_mul]

      have ha :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis a) ξ

      unfold h3FourierGradientMagnitude at ha

      calc
        ‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis a) ξ‖ *
            ‖third ξ‖
            ≤
          ((2 * Real.pi) * ‖ξ‖) * ‖third ξ‖ :=
          mul_le_mul_of_nonneg_right
            ha
            (norm_nonneg _)
        _ =
          (2 * Real.pi) *
            (‖ξ‖ * ‖third ξ‖) := by
          ring

  dsimp only [fourth, third, N, W] at hFourthInt
  exact hFourthInt

/-- The literal ordered fourth selected spatial derivative is the ordinary
inverse Fourier reconstruction of its ordered fourth multiplier. -/
theorem h3SelectedRestartRealVelocity_spatial_d_four_eq_fourierInvFourth
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (spatial3.d d
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W t i)))))
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
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis d) ξ *
                  h3SpectralScalarRawFourier
                    (W t i) ξ))))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier (W t i)

  let third : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis b) ξ *
        (h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis d) ξ *
            N ξ))

  let fourth : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        third ξ

  have hThirdInt :
      Integrable third
        (volume : Measure H3FourierPoint3) := by
    dsimp only [third, N, W]
    exact
      h3SelectedRestartRawThirdCoordinate_integrable
        hν U₀ hA hU₀ ht htR i b c d

  have hNFourthMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        4 hν U₀ hA hU₀ ht htR.le i

  have hThirdMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖third ξ‖)
        (volume : Measure H3FourierPoint3) := by

    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 3 *
              (‖ξ‖ ^ 4 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNFourthMoment.const_mul ((2 * Real.pi) ^ 3)

    apply hDom.mono'

    · exact
        continuous_norm.aestronglyMeasurable.mul
          hThirdInt.aestronglyMeasurable.norm

    · filter_upwards with ξ
      dsimp only [third]

      have hb :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis b) ξ
      have hc :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ
      have hd :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis d) ξ

      unfold h3FourierGradientMagnitude at hb hc hd

      have hLeft0 :
          0 ≤
            ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ *
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ *
                    N ξ))‖ := by
        positivity

      have hRight0 :
          0 ≤
            (2 * Real.pi) ^ 3 *
              (‖ξ‖ ^ 4 * ‖N ξ‖) := by
        positivity

      have hBound :
          ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ *
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ *
                    N ξ))‖
            ≤
          (2 * Real.pi) ^ 3 *
            (‖ξ‖ ^ 4 * ‖N ξ‖) := by

        rw [norm_mul, norm_mul, norm_mul]

        calc
          ‖ξ‖ *
              (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ‖ *
                (‖h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ‖ *
                  (‖h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ‖ *
                    ‖N ξ‖)))
              ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (‖h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ‖ *
                  (‖h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ‖ *
                    ‖N ξ‖))) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hb
                  (mul_nonneg
                    (norm_nonneg _)
                    (mul_nonneg
                      (norm_nonneg _)
                      (norm_nonneg _))))
                (norm_nonneg ξ)
          _ ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (((2 * Real.pi) * ‖ξ‖) *
                  (‖h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ‖ *
                    ‖N ξ‖))) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right
                    hc
                    (mul_nonneg
                      (norm_nonneg _)
                      (norm_nonneg _)))
                  (by positivity))
                (norm_nonneg ξ)
          _ ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (((2 * Real.pi) * ‖ξ‖) *
                  (((2 * Real.pi) * ‖ξ‖) *
                    ‖N ξ‖))) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right
                      hd
                      (norm_nonneg _))
                    (by positivity))
                  (by positivity))
                (norm_nonneg ξ)
          _ =
            (2 * Real.pi) ^ 3 *
              (‖ξ‖ ^ 4 * ‖N ξ‖) := by
            ring

      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeft0,
        abs_of_nonneg hRight0
      ] using hBound

  have hCubic :=
    h3SelectedRestartRealVelocity_spatial_d_three_eq_fourierInvThird
      hν U₀ hA hU₀ ht htR i b c d

  have hFourthEq :
      spatial3.d a
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv third
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv fourth
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    funext x
    dsimp only [fourth]
    exact
      fourierInv_re_onPoint3_spatialDerivative_eq_h3SelectedRawSecond
        hThirdInt hThirdMoment a x

  have hCubic' :
      spatial3.d b
          (spatial3.d c
            (spatial3.d d
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W t i))))
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv third
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    simpa only [third, N, W] using hCubic

  calc
    spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d d
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W t i)))))
        =
      spatial3.d a
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv third
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) :=
      congrArg (spatial3.d a) hCubic'
    _ =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv fourth
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) :=
      hFourthEq
    _ =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          (fun ξ : H3FourierPoint3 =>
            h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis a) ξ *
              (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ *
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ *
                    h3SpectralScalarRawFourier
                      (W t i) ξ))))
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
      rfl

/-! ## The continuous physical package has the literal fourth jet -/

/-- The transported physical fourth-coordinate package has the ordinary
inverse-Fourier multiplier as an a.e. representative. -/
theorem h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2_ae_eq_fourierInv
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
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
    (((h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2
        hNS ht₀ hE hTail q j a b c d : H3ScalarL2) :
        Point3 → ℝ)
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
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis d) ξ *
                  h3SpectralScalarRawFourier
                    (W (q : ℝ) j) ξ))))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)) := by
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀

  let raw : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        (h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis d) ξ *
              h3SpectralScalarRawFourier
                (W (q : ℝ) j) ξ)))

  let f2 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFourthCoordinateFourierL2
      hNS ht₀ hE hTail q j a b c d

  let u2 : H3FourierComplexL2 :=
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm f2

  let r2 : H3FourierRealL2 :=
    h3RealPartFourierL2 u2

  have hRawInt :
      Integrable raw
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, W, U₀, hA, hU₀]
    exact
      h3SelectedRestartRawFourthCoordinate_integrable
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        q.property.1
        q.property.2
        j a b c d

  have hRaw2 :
      MemLp raw 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, W, U₀, hA, hU₀]
    exact
      h3PreterminalSelectedVelocityFourthCoordinate_memLp2
        hNS ht₀ hE hTail q j a b c d

  have hCompat :
      FourierTransformInv.fourierInv raw
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2]
    unfold h3PreterminalSelectedVelocityFourthCoordinateFourierL2
    exact
      h3FourierInv_integrable_memLp2_ae_eq_L2
        hRawInt hRaw2

  have hCompatPoint :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((u2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hCompat

  have hRe :
      ((r2 : H3FourierRealL2) :
        H3FourierPoint3 → ℝ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (((u2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ).re) := by
    dsimp only [r2]
    unfold h3RealPartFourierL2
    exact Complex.reCLM.coeFn_compLp u2

  have hRePoint :
      (fun x : Point3 =>
        ((r2 : H3FourierRealL2) :
          H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (((u2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hRe

  have hFrom :
      (((h3FromFourierRealL2 r2 : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((r2 : H3FourierRealL2) :
          H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))) := by
    unfold h3FromFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        r2
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hAE :
      (((h3FromFourierRealL2 r2 : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)) := by
    filter_upwards [
      hFrom, hRePoint, hCompatPoint
    ] with x hxFrom hxRe hxCompat

    calc
      ((h3FromFourierRealL2 r2 : H3ScalarL2) :
          Point3 → ℝ) x
          =
        ((r2 : H3FourierRealL2) :
          H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x) :=
        hxFrom
      _ =
        (((u2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re :=
        hxRe
      _ =
        (FourierTransformInv.fourierInv raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re :=
        congrArg Complex.re hxCompat.symm

  simpa only [
    h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2,
    r2, u2, f2, raw, W, U₀, hA, hU₀
  ] using hAE

/-- At a strict canonical selected time, the continuous physical package is
a.e. the literal ordered fourth derivative of the scalar selected component. -/
theorem h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2_ae_eq_spatial_d_four
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
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
    (((h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2
        hNS ht₀ hE hTail q j a b c d : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (spatial3.d d
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W (q : ℝ) j)))))) := by
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀

  have hInv :=
    h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2_ae_eq_fourierInv
      hNS ht₀ hE hTail q j a b c d

  have hPoint :=
    h3SelectedRestartRealVelocity_spatial_d_four_eq_fourierInvFourth
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      q.property.1
      q.property.2
      j a b c d

  filter_upwards [hInv] with x hx
  rw [hx]
  exact congrFun hPoint x |>.symm

/-! ## Literal fourth selected velocity L² path -/

/-- Canonical `H3ScalarL2` state carried by the literal ordered fourth
derivative of one selected real velocity component. -/
noncomputable def h3PreterminalSelectedRealVelocityFourthCoordinateL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j a b c d : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  (h3CanonicalSelectedArbitraryFourthVelocityJetMemLp2OnRestartRadius_closed
      E u T t₀ hNS ht₀ hE hTail
      (q : ℝ) q.property
      a b c d j).toLp
    (spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (spatial3.d d
            (fun y : Point3 =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState
                  hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                (q : ℝ) y).component j)))))

/-- The literal fourth-jet package equals the continuous physical
reconstruction with the corresponding finite velocity coordinate. -/
theorem h3PreterminalSelectedRealVelocityFourthCoordinateL2_eq_physicalL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j a b c d : PrimeTensor.Axis Depth.three) :
    h3PreterminalSelectedRealVelocityFourthCoordinateL2
        hNS ht₀ hE hTail q j a b c d
      =
    h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2
      hNS ht₀ hE hTail q
      (h3ClassicalizationFinOfAxis j)
      a b c d := by

  apply MeasureTheory.Lp.ext

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀

  let jf : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hAxisJ :
      h3AxisOfFin3 jf = j := by
    dsimp only [jf]
    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis j

  have hComponent :
      (fun y : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀
          (q : ℝ) y).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W (q : ℝ) jf) := by
    funext y
    rw [← hAxisJ]
    simp only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      W
    ]

  have hLiteral :
      (((h3PreterminalSelectedRealVelocityFourthCoordinateL2
          hNS ht₀ hE hTail q j a b c d :
          H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d d
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W (q : ℝ) jf)))))) := by

    let selectedSlice : ScalarField3 :=
      fun y : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          (q : ℝ) y).component j

    have hSpatial :
        spatial3.d a
            (spatial3.d b
              (spatial3.d c
                (spatial3.d d selectedSlice)))
          =
        spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (spatial3.d d
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W (q : ℝ) jf))))) := by
      exact
        congrArg
          (fun f : ScalarField3 =>
            spatial3.d a
              (spatial3.d b
                (spatial3.d c
                  (spatial3.d d f))))
          (by
            dsimp only [selectedSlice]
            exact hComponent)

    have hToLp :
        (((h3PreterminalSelectedRealVelocityFourthCoordinateL2
            hNS ht₀ hE hTail q j a b c d :
            H3ScalarL2) :
            Point3 → ℝ)
          =ᵐ[(volume : Measure Point3)]
        spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (spatial3.d d selectedSlice)))) := by
      unfold h3PreterminalSelectedRealVelocityFourthCoordinateL2
      dsimp only [selectedSlice]
      exact
        MeasureTheory.MemLp.coeFn_toLp
          (h3CanonicalSelectedArbitraryFourthVelocityJetMemLp2OnRestartRadius_closed
            E u T t₀ hNS ht₀ hE hTail
            (q : ℝ) q.property
            a b c d j)

    exact
      hToLp.trans
        (Filter.Eventually.of_forall
          (fun x => congrFun hSpatial x))

  have hPackage :=
    h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2_ae_eq_spatial_d_four
      hNS ht₀ hE hTail q jf a b c d

  filter_upwards [
    hLiteral, hPackage
  ] with x hxLiteral hxPackage

  exact
    hxLiteral.trans hxPackage.symm

/-- Every literal ordered fourth selected velocity coordinate is strongly
continuous in physical `L²` on the strict restart interval. -/
theorem continuous_h3PreterminalSelectedRealVelocityFourthCoordinateL2OnRestartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j a b c d : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedRealVelocityFourthCoordinateL2
          hNS ht₀ hE hTail q j a b c d) := by

  have hPhysical :=
    continuous_h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2OnRestartRadius
      hNS ht₀ hE hTail
      (h3ClassicalizationFinOfAxis j)
      a b c d

  have hEq :
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedRealVelocityFourthCoordinateL2
          hNS ht₀ hE hTail q j a b c d)
        =
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedVelocityFourthCoordinatePhysicalL2
          hNS ht₀ hE hTail q
          (h3ClassicalizationFinOfAxis j)
          a b c d) := by
    funext q
    exact
      h3PreterminalSelectedRealVelocityFourthCoordinateL2_eq_physicalL2
        hNS ht₀ hE hTail q j a b c d

  rw [hEq]
  exact hPhysical

/-- Repeated-index fourth-coordinate specialization needed by the order-two
differentiated Laplacian. -/
theorem continuous_h3PreterminalSelectedRealVelocityRepeatedFourthCoordinateL2OnRestartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j a b k : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedRealVelocityFourthCoordinateL2
          hNS ht₀ hE hTail q j a b k k) := by
  exact
    continuous_h3PreterminalSelectedRealVelocityFourthCoordinateL2OnRestartRadius
      hNS ht₀ hE hTail j a b k k

end

end Euclidean
end Bridge
end PrimeTensor
