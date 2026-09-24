import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Three.Selected.Velocity.Fifth.Coordinate.Physical.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Velocity.Fourth.Coordinate.Physical.L2.Identification
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Three.Selected.Temporal.L2.Reduction

/-!
# Identify the continuous selected fifth-coordinate physical L² package

The preceding checkpoints proved strong physical `L²` continuity of every
ordered fifth selected Fourier coordinate.  This file identifies that package
with the literal ordered fifth spatial derivative of the selected real
velocity.

The proof adds one derivative to the already-closed fourth-coordinate
identification.  If

    fourth(ξ) = d_b(ξ) d_c(ξ) d_d(ξ) d_e(ξ) N(ξ),

then the fifth raw moment controls `|ξ| |fourth(ξ)|` in `L¹`.  One further
application of the inverse-Fourier derivative bridge therefore identifies

    D_a D_b D_c D_d D_e u

with the inverse transform of the ordered fifth multiplier.

For the order-three PDE only the repeated shape `(a,b,c,k,k)` is needed.
Accordingly the final literal `H3ScalarL2` path is packaged only in that shape,
using the already-closed selected fourth/fifth high-jet theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform LineDeriv Topology
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedVelocityFifthCoordinatePhysicalL2Identification
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderThreeSelectedVelocityFifthCoordinatePhysicalL2Identification :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## One more derivative beyond the fourth-coordinate bridge -/

/-- At strict positive selected restart times the literal ordered fifth
coordinate Fourier multiplier is integrable. -/
theorem h3SelectedRestartRawFifthCoordinate_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c d e : PrimeTensor.Axis Depth.three) :
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
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis e) ξ *
                  h3SpectralScalarRawFourier (W t i) ξ)))))
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier (W t i)

  let fourth : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis b) ξ *
        (h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis d) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis e) ξ *
              N ξ)))

  let fifth : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        fourth ξ

  have hFourthInt :
      Integrable fourth
        (volume : Measure H3FourierPoint3) := by
    dsimp only [fourth, N, W]
    exact
      h3SelectedRestartRawFourthCoordinate_integrable
        hν U₀ hA hU₀ ht htR i b c d e

  have hNFifthMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        5 hν U₀ hA hU₀ ht htR.le i

  have hFourthMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖fourth ξ‖)
        (volume : Measure H3FourierPoint3) := by

    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 4 *
              (‖ξ‖ ^ 5 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNFifthMoment.const_mul ((2 * Real.pi) ^ 4)

    apply hDom.mono'

    · exact
        continuous_norm.aestronglyMeasurable.mul
          hFourthInt.aestronglyMeasurable.norm

    · filter_upwards with ξ

      dsimp only [fourth]

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

      unfold h3FourierGradientMagnitude at hb hc hd he

      have hLeft0 :
          0 ≤
            ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ *
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ *
                    (h3FourierDerivativeSymbol
                        (h3ClassicalizationFinOfAxis e) ξ *
                      N ξ)))‖ := by
        positivity

      have hRight0 :
          0 ≤
            (2 * Real.pi) ^ 4 *
              (‖ξ‖ ^ 5 * ‖N ξ‖) := by
        positivity

      have hBound :
          ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ *
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ *
                    (h3FourierDerivativeSymbol
                        (h3ClassicalizationFinOfAxis e) ξ *
                      N ξ)))‖
            ≤
          (2 * Real.pi) ^ 4 *
            (‖ξ‖ ^ 5 * ‖N ξ‖) := by

        rw [norm_mul, norm_mul, norm_mul, norm_mul]

        calc
          ‖ξ‖ *
              (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ‖ *
                (‖h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ‖ *
                  (‖h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ‖ *
                    (‖h3FourierDerivativeSymbol
                        (h3ClassicalizationFinOfAxis e) ξ‖ *
                      ‖N ξ‖))))
              ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (((2 * Real.pi) * ‖ξ‖) *
                  (((2 * Real.pi) * ‖ξ‖) *
                    (((2 * Real.pi) * ‖ξ‖) *
                      ‖N ξ‖)))) := by
            gcongr
          _ =
            (2 * Real.pi) ^ 4 *
              (‖ξ‖ ^ 5 * ‖N ξ‖) := by
            ring

      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeft0,
        abs_of_nonneg hRight0
      ] using hBound

  have hFifthInt :
      Integrable fifth
        (volume : Measure H3FourierPoint3) := by

    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) *
              (‖ξ‖ * ‖fourth ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hFourthMoment.const_mul (2 * Real.pi)

    apply hDom.mono'

    · dsimp only [fifth]
      exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis a)).aestronglyMeasurable.mul
          hFourthInt.aestronglyMeasurable

    · filter_upwards with ξ
      dsimp only [fifth]
      rw [norm_mul]

      have ha :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis a) ξ

      unfold h3FourierGradientMagnitude at ha

      calc
        ‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis a) ξ‖ *
            ‖fourth ξ‖
            ≤
          ((2 * Real.pi) * ‖ξ‖) * ‖fourth ξ‖ :=
          mul_le_mul_of_nonneg_right
            ha
            (norm_nonneg _)
        _ =
          (2 * Real.pi) *
            (‖ξ‖ * ‖fourth ξ‖) := by
          ring

  dsimp only [fifth, fourth, N, W] at hFifthInt
  exact hFifthInt

/-- The literal ordered fifth selected spatial derivative is the ordinary
inverse Fourier reconstruction of its ordered fifth multiplier. -/
theorem h3SelectedRestartRealVelocity_spatial_d_five_eq_fourierInvFifth
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c d e : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (spatial3.d d
            (spatial3.d e
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W t i))))))
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
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis e) ξ *
                    h3SpectralScalarRawFourier
                      (W t i) ξ)))))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier (W t i)

  let fourth : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis b) ξ *
        (h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis d) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis e) ξ *
              N ξ)))

  let fifth : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        fourth ξ

  have hFourthInt :
      Integrable fourth
        (volume : Measure H3FourierPoint3) := by
    dsimp only [fourth, N, W]
    exact
      h3SelectedRestartRawFourthCoordinate_integrable
        hν U₀ hA hU₀ ht htR i b c d e

  have hNFifthMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        5 hν U₀ hA hU₀ ht htR.le i

  have hFourthMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖fourth ξ‖)
        (volume : Measure H3FourierPoint3) := by

    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 4 *
              (‖ξ‖ ^ 5 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNFifthMoment.const_mul ((2 * Real.pi) ^ 4)

    apply hDom.mono'

    · exact
        continuous_norm.aestronglyMeasurable.mul
          hFourthInt.aestronglyMeasurable.norm

    · filter_upwards with ξ
      dsimp only [fourth]

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

      unfold h3FourierGradientMagnitude at hb hc hd he

      have hLeft0 :
          0 ≤
            ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ *
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ *
                    (h3FourierDerivativeSymbol
                        (h3ClassicalizationFinOfAxis e) ξ *
                      N ξ)))‖ := by
        positivity

      have hRight0 :
          0 ≤
            (2 * Real.pi) ^ 4 *
              (‖ξ‖ ^ 5 * ‖N ξ‖) := by
        positivity

      have hBound :
          ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ *
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ *
                    (h3FourierDerivativeSymbol
                        (h3ClassicalizationFinOfAxis e) ξ *
                      N ξ)))‖
            ≤
          (2 * Real.pi) ^ 4 *
            (‖ξ‖ ^ 5 * ‖N ξ‖) := by

        rw [norm_mul, norm_mul, norm_mul, norm_mul]

        calc
          ‖ξ‖ *
              (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ‖ *
                (‖h3FourierDerivativeSymbol
                    (h3ClassicalizationFinOfAxis c) ξ‖ *
                  (‖h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis d) ξ‖ *
                    (‖h3FourierDerivativeSymbol
                        (h3ClassicalizationFinOfAxis e) ξ‖ *
                      ‖N ξ‖))))
              ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (((2 * Real.pi) * ‖ξ‖) *
                  (((2 * Real.pi) * ‖ξ‖) *
                    (((2 * Real.pi) * ‖ξ‖) *
                      ‖N ξ‖)))) := by
            gcongr
          _ =
            (2 * Real.pi) ^ 4 *
              (‖ξ‖ ^ 5 * ‖N ξ‖) := by
            ring

      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeft0,
        abs_of_nonneg hRight0
      ] using hBound

  have hFourth :=
    h3SelectedRestartRealVelocity_spatial_d_four_eq_fourierInvFourth
      hν U₀ hA hU₀ ht htR i b c d e

  have hFifthEq :
      spatial3.d a
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv fourth
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv fifth
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    funext x
    dsimp only [fifth]
    exact
      fourierInv_re_onPoint3_spatialDerivative_eq_h3SelectedRawSecond
        hFourthInt hFourthMoment a x

  have hFourth' :
      spatial3.d b
          (spatial3.d c
            (spatial3.d d
              (spatial3.d e
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W t i)))))
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv fourth
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    simpa only [fourth, N, W] using hFourth

  calc
    spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d d
              (spatial3.d e
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W t i))))))
        =
      spatial3.d a
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv fourth
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) :=
      congrArg (spatial3.d a) hFourth'
    _ =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv fifth
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) :=
      hFifthEq
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
                    (h3FourierDerivativeSymbol
                        (h3ClassicalizationFinOfAxis e) ξ *
                      h3SpectralScalarRawFourier
                        (W t i) ξ)))))
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
      rfl

/-! ## The continuous physical package has the literal fifth jet -/

theorem h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2_ae_eq_fourierInv
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
    (((h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2
        hNS ht₀ hE hTail q j a b c d e : H3ScalarL2) :
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
                  (h3FourierDerivativeSymbol
                      (h3ClassicalizationFinOfAxis e) ξ *
                    h3SpectralScalarRawFourier
                      (W (q : ℝ) j) ξ)))))
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
              (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis e) ξ *
                h3SpectralScalarRawFourier
                  (W (q : ℝ) j) ξ))))

  let f2 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthCoordinateFourierL2
      hNS ht₀ hE hTail q j a b c d e

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
      h3SelectedRestartRawFifthCoordinate_integrable
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        q.property.1 q.property.2
        j a b c d e

  have hRaw2 :
      MemLp raw 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, W, U₀, hA, hU₀]
    exact
      h3PreterminalSelectedVelocityFifthCoordinate_memLp2
        hNS ht₀ hE hTail q j a b c d e

  have hCompat :
      FourierTransformInv.fourierInv raw
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2]
    unfold h3PreterminalSelectedVelocityFifthCoordinateFourierL2
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
    h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2,
    r2, u2, f2, raw, W, U₀, hA, hU₀
  ] using hAE

theorem h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2_ae_eq_spatial_d_five
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
    (((h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2
        hNS ht₀ hE hTail q j a b c d e : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (spatial3.d d
            (spatial3.d e
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W (q : ℝ) j))))))) := by
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
    h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2_ae_eq_fourierInv
      hNS ht₀ hE hTail q j a b c d e

  have hPoint :=
    h3SelectedRestartRealVelocity_spatial_d_five_eq_fourierInvFifth
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      q.property.1 q.property.2
      j a b c d e

  filter_upwards [hInv] with x hx
  rw [hx]
  exact congrFun hPoint x |>.symm

/-! ## Repeated fifth selected velocity L² path -/

/-- Canonical `H3ScalarL2` state carried by the repeated-index fifth derivative
`D_a D_b D_c D_k D_k` of one selected real velocity component. -/
noncomputable def h3PreterminalSelectedRealVelocityRepeatedFifthCoordinateL2
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
    (j a b c k : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  ((h3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius_closed_for_order3
      E u T t₀ hNS ht₀ hE hTail
      (q : ℝ) q.property).2
      a b c k j).toLp
    (spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (spatial3.d k
            (spatial3.d k
              (fun y : Point3 =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState
                    hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  (q : ℝ) y).component j))))))

theorem h3PreterminalSelectedRealVelocityRepeatedFifthCoordinateL2_eq_physicalL2
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
    (j a b c k : PrimeTensor.Axis Depth.three) :
    h3PreterminalSelectedRealVelocityRepeatedFifthCoordinateL2
        hNS ht₀ hE hTail q j a b c k
      =
    h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2
      hNS ht₀ hE hTail q
      (h3ClassicalizationFinOfAxis j)
      a b c k k := by

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
    exact h3AxisOfFin3_h3ClassicalizationFinOfAxis j

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

  have hSliceEq :
      selectedSlice
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W (q : ℝ) jf) := by
    simpa only [selectedSlice, U₀, hA, hU₀] using hComponent

  have hSpatial :
      spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (spatial3.d k
                (spatial3.d k selectedSlice))))
        =
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d k
              (spatial3.d k
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W (q : ℝ) jf)))))) := by
    exact
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d a
            (spatial3.d b
              (spatial3.d c
                (spatial3.d k
                  (spatial3.d k f)))))
        hSliceEq

  have hLiteral :
      (((h3PreterminalSelectedRealVelocityRepeatedFifthCoordinateL2
          hNS ht₀ hE hTail q j a b c k :
          H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d k
              (spatial3.d k
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W (q : ℝ) jf))))))) := by

    have hToLp :
        (((h3PreterminalSelectedRealVelocityRepeatedFifthCoordinateL2
            hNS ht₀ hE hTail q j a b c k :
            H3ScalarL2) :
            Point3 → ℝ)
          =ᵐ[(volume : Measure Point3)]
        spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (spatial3.d k
                (spatial3.d k selectedSlice))))) := by
      simpa only [
        h3PreterminalSelectedRealVelocityRepeatedFifthCoordinateL2,
        selectedSlice
      ] using
        (MeasureTheory.MemLp.coeFn_toLp
          ((h3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius_closed_for_order3
            E u T t₀ hNS ht₀ hE hTail
            (q : ℝ) q.property).2
            a b c k j))


    filter_upwards [hToLp] with x hx
    exact hx.trans (congrFun hSpatial x)

  have hPackage :=
    h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2_ae_eq_spatial_d_five
      hNS ht₀ hE hTail q jf a b c k k

  filter_upwards [
    hLiteral, hPackage
  ] with x hxLiteral hxPackage

  exact hxLiteral.trans hxPackage.symm

/-- The repeated fifth selected velocity coordinate required by the
order-three differentiated Laplacian is strongly continuous in physical
`L²` on the strict restart interval. -/
theorem continuous_h3PreterminalSelectedRealVelocityRepeatedFifthCoordinateL2OnRestartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j a b c k : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedRealVelocityRepeatedFifthCoordinateL2
          hNS ht₀ hE hTail q j a b c k) := by

  have hPhysical :=
    continuous_h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2OnRestartRadius
      hNS ht₀ hE hTail
      (h3ClassicalizationFinOfAxis j)
      a b c k k

  have hEq :
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedRealVelocityRepeatedFifthCoordinateL2
          hNS ht₀ hE hTail q j a b c k)
        =
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedVelocityFifthCoordinatePhysicalL2
          hNS ht₀ hE hTail q
          (h3ClassicalizationFinOfAxis j)
          a b c k k) := by
    funext q
    exact
      h3PreterminalSelectedRealVelocityRepeatedFifthCoordinateL2_eq_physicalL2
        hNS ht₀ hE hTail q j a b c k

  rw [hEq]
  exact hPhysical

end

end Euclidean
end Bridge
end PrimeTensor
