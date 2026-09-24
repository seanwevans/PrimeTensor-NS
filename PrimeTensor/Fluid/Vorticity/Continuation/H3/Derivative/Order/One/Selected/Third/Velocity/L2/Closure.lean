import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Temporal.L2.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Duhamel.Tail.Cubic.L2.Baseline
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Raw.Forcing.Physical.L2.Third
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Mixed.Derivative.Candidate.Bridge

/-!
# Close the selected cubic velocity L² frontier for order one

The order-one temporal coefficient reduction asks only for the repeated-index
selected cubic velocity fields

    ∂ₐ ∂ₖ ∂ₖ Sⱼ

to belong to physical `L²`.

No positive-time smoothing gain is needed here.  Every H³ spectral scalar state
already satisfies

    ‖ξ‖³ raw(G)(ξ) ∈ L²,

because the exact H³ weight dominates the cubic radial weight.

For one selected scalar coordinate, use the standard coordinate-symbol bound to
upgrade this radial statement to `L²` for every ordered triple of coordinate
multipliers.  The selected positive-time all-orders moment theorem supplies
the `L¹` moments required to differentiate the ordinary inverse Fourier
representative three times.  The existing public one-coordinate inverse
Fourier derivative bridge is then iterated three times.

Consequently every ordered selected third spatial velocity derivative belongs
to physical `L²`, and in particular the repeated-index frontier from
`H3PathOrderOneSelectedTemporalL2Reduction` closes outright.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform LineDeriv Topology
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedThirdVelocityL2Closure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderOneSelectedThirdVelocityL2Closure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every ordered third spatial derivative of one selected real velocity
coordinate belongs to physical `L²` at a strict positive restart time. -/
theorem h3SelectedRestartRealVelocity_spatial_d_three_memLp2
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
    MemLp
      (spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W t i)))))
      2
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let H : H3SpectralScalarState :=
    W t i

  let N : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier H

  let af : Fin 3 := h3ClassicalizationFinOfAxis a
  let bf : Fin 3 := h3ClassicalizationFinOfAxis b
  let cf : Fin 3 := h3ClassicalizationFinOfAxis c

  let first : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol cf ξ * N ξ

  let second : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol bf ξ *
        (h3FourierDerivativeSymbol cf ξ * N ξ)

  let third : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol af ξ *
        (h3FourierDerivativeSymbol bf ξ *
          (h3FourierDerivativeSymbol cf ξ * N ξ))

  have hNInt :
      Integrable N
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 H)

  have hNFirstMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, H, W]
    simpa only [pow_one] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        1 hν U₀ hA hU₀ ht htR.le i

  have hNSecondMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, H, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        2 hν U₀ hA hU₀ ht htR.le i

  have hNThirdMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, H, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ ht htR.le i

  have hFirstInt :
      Integrable first
        (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) * (‖ξ‖ * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNFirstMoment.const_mul (2 * Real.pi)

    apply hDom.mono'
    · dsimp only [first, cf]
      exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis c)).aestronglyMeasurable.mul
          hNInt.aestronglyMeasurable
    · filter_upwards with ξ

      dsimp only [first, cf]

      rw [norm_mul]

      have hDeriv :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ

      unfold h3FourierGradientMagnitude at hDeriv

      calc
        ‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ‖ *
              ‖N ξ‖
            ≤
          ((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖ :=
          mul_le_mul_of_nonneg_right
            hDeriv
            (norm_nonneg _)
        _ =
          (2 * Real.pi) * (‖ξ‖ * ‖N ξ‖) := by
          ring

  have hFirstMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖first ξ‖)
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

      dsimp only [first, cf]

      have hLeftNonneg :
          0 ≤
            ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ *
                N ξ‖ := by
        positivity

      have hRightNonneg :
          0 ≤
            (2 * Real.pi) *
              (‖ξ‖ ^ 2 * ‖N ξ‖) := by
        positivity

      have hDeriv :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ

      unfold h3FourierGradientMagnitude at hDeriv

      have hBound :
          ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ *
                N ξ‖
            ≤
          (2 * Real.pi) *
            (‖ξ‖ ^ 2 * ‖N ξ‖) := by
        rw [norm_mul]

        calc
          ‖ξ‖ *
              (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ‖ *
                ‖N ξ‖)
              ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                ‖N ξ‖) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hDeriv
                  (norm_nonneg _))
                (norm_nonneg ξ)
          _ =
            (2 * Real.pi) *
              (‖ξ‖ ^ 2 * ‖N ξ‖) := by
            ring

      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeftNonneg,
        abs_of_nonneg hRightNonneg
      ] using hBound

  have hSecondInt :
      Integrable second
        (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 2 *
              (‖ξ‖ ^ 2 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNSecondMoment.const_mul ((2 * Real.pi) ^ 2)

    apply hDom.mono'
    · dsimp only [second, bf, cf]
      exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis b)).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous
            (h3ClassicalizationFinOfAxis c)).aestronglyMeasurable.mul
            hNInt.aestronglyMeasurable)
    · filter_upwards with ξ

      dsimp only [second, bf, cf]

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
              (h3ClassicalizationFinOfAxis c) ξ‖ *
              ‖N ξ‖)
            ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ‖ *
              ‖N ξ‖) := by
          exact
            mul_le_mul_of_nonneg_right
              hb
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (((2 * Real.pi) * ‖ξ‖) *
              ‖N ξ‖) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                hc
                (norm_nonneg _))
              (by positivity)
        _ =
          (2 * Real.pi) ^ 2 *
            (‖ξ‖ ^ 2 * ‖N ξ‖) := by
          ring

  have hSecondMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖second ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 2 *
              (‖ξ‖ ^ 3 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNThirdMoment.const_mul ((2 * Real.pi) ^ 2)

    apply hDom.mono'
    · exact
        continuous_norm.aestronglyMeasurable.mul
          hSecondInt.aestronglyMeasurable.norm
    · filter_upwards with ξ

      dsimp only [second, bf, cf]

      have hLeftNonneg :
          0 ≤
            ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ *
                  N ξ)‖ := by
        positivity

      have hRightNonneg :
          0 ≤
            (2 * Real.pi) ^ 2 *
              (‖ξ‖ ^ 3 * ‖N ξ‖) := by
        positivity

      have hb :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis b) ξ

      have hc :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ

      unfold h3FourierGradientMagnitude at hb hc

      have hBound :
          ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ *
                  N ξ)‖
            ≤
          (2 * Real.pi) ^ 2 *
            (‖ξ‖ ^ 3 * ‖N ξ‖) := by
        rw [norm_mul, norm_mul]

        calc
          ‖ξ‖ *
              (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ‖ *
                (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ‖ *
                  ‖N ξ‖))
              ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ‖ *
                  ‖N ξ‖)) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hb
                  (mul_nonneg
                    (norm_nonneg _)
                    (norm_nonneg _)))
                (norm_nonneg ξ)
          _ ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                (((2 * Real.pi) * ‖ξ‖) *
                  ‖N ξ‖)) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right
                    hc
                    (norm_nonneg _))
                  (by positivity))
                (norm_nonneg ξ)
          _ =
            (2 * Real.pi) ^ 2 *
              (‖ξ‖ ^ 3 * ‖N ξ‖) := by
            ring

      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeftNonneg,
        abs_of_nonneg hRightNonneg
      ] using hBound

  have hThirdInt :
      Integrable third
        (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 3 *
              (‖ξ‖ ^ 3 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNThirdMoment.const_mul ((2 * Real.pi) ^ 3)

    apply hDom.mono'
    · dsimp only [third, af, bf, cf]
      exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis a)).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous
            (h3ClassicalizationFinOfAxis b)).aestronglyMeasurable.mul
            ((h3FourierDerivativeSymbol_continuous
              (h3ClassicalizationFinOfAxis c)).aestronglyMeasurable.mul
              hNInt.aestronglyMeasurable))
    · filter_upwards with ξ

      dsimp only [third, af, bf, cf]

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
                (h3ClassicalizationFinOfAxis c) ξ‖ *
                ‖N ξ‖))
            ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis b) ξ‖ *
              (‖h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis c) ξ‖ *
                ‖N ξ‖)) := by
          exact
            mul_le_mul_of_nonneg_right
              ha
              (mul_nonneg
                (norm_nonneg _)
                (mul_nonneg
                  (norm_nonneg _)
                  (norm_nonneg _)))
        _ ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (((2 * Real.pi) * ‖ξ‖) *
              (‖h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis c) ξ‖ *
                ‖N ξ‖)) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                hb
                (mul_nonneg
                  (norm_nonneg _)
                  (norm_nonneg _)))
              (by positivity)
        _ ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (((2 * Real.pi) * ‖ξ‖) *
              (((2 * Real.pi) * ‖ξ‖) *
                ‖N ξ‖)) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hc
                  (norm_nonneg _))
                (by positivity))
              (by positivity)
        _ =
          (2 * Real.pi) ^ 3 *
            (‖ξ‖ ^ 3 * ‖N ξ‖) := by
          ring

  have hRadial :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 3 : ℝ) : ℂ) * N ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3SpectralScalarRawFourier_cubicWeight_memLp2 H

  have hThird2 :
      MemLp third
        2
        (volume : Measure H3FourierPoint3) := by
    refine
      hRadial.of_le_mul
        (c := (2 * Real.pi) ^ 3)
        hThirdInt.aestronglyMeasurable
        ?_

    filter_upwards with ξ

    dsimp only [third, af, bf, cf]

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

    have hGrad0 :
        0 ≤ h3FourierGradientMagnitude ξ := by
      unfold h3FourierGradientMagnitude
      positivity

    calc
      ‖h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ‖ *
          (‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ‖ *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ‖ *
              ‖N ξ‖))
          ≤
        h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ‖ *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ‖ *
              ‖N ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg
                (norm_nonneg _)
                (norm_nonneg _)))
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ‖ *
              ‖N ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hb
              (mul_nonneg
                (norm_nonneg _)
                (norm_nonneg _)))
            hGrad0
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (h3FourierGradientMagnitude ξ *
              ‖N ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                hc
                (norm_nonneg _))
              hGrad0)
            hGrad0
      _ =
        (2 * Real.pi) ^ 3 *
          ‖((‖ξ‖ ^ 3 : ℝ) : ℂ) * N ξ‖ := by
        unfold h3FourierGradientMagnitude
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [
          abs_of_nonneg
            (pow_nonneg (norm_nonneg ξ) 3)
        ]
        ring

  have hComplex :
      MemLp
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            third
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x))
        2
        (volume : Measure Point3) :=
    memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedRawSecond
      hThirdInt hThird2

  have hReal :
      MemLp
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            third
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)).re)
        2
        (volume : Measure Point3) :=
    memLp_re_of_memLp_complex_h3SelectedRawSecond
      hComplex

  have hFirstEq :
      spatial3.d c
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv
              N
              ((WithLp.toLp 2 :
                Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          first
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re) := by
    funext x

    dsimp only [first, cf]

    exact
      fourierInv_re_onPoint3_spatialDerivative_eq_h3SelectedRawSecond
        hNInt hNFirstMoment c x

  have hSecondEq :
      spatial3.d b
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv
              first
              ((WithLp.toLp 2 :
                Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          second
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re) := by
    funext x

    dsimp only [second, first, bf]

    exact
      fourierInv_re_onPoint3_spatialDerivative_eq_h3SelectedRawSecond
        hFirstInt hFirstMoment b x

  have hThirdEq :
      spatial3.d a
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv
              second
              ((WithLp.toLp 2 :
                Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          third
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re) := by
    funext x

    dsimp only [third, second, af]

    exact
      fourierInv_re_onPoint3_spatialDerivative_eq_h3SelectedRawSecond
        hSecondInt hSecondMoment a x

  have hEq :
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (fun x : Point3 =>
              (FourierTransformInv.fourierInv
                N
                ((WithLp.toLp 2 :
                  Point3 → H3FourierPoint3) x)).re)))
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          third
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re) := by
    calc
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (fun x : Point3 =>
              (FourierTransformInv.fourierInv
                N
                ((WithLp.toLp 2 :
                  Point3 → H3FourierPoint3) x)).re)))
          =
        spatial3.d a
          (spatial3.d b
            (fun x : Point3 =>
              (FourierTransformInv.fourierInv
                first
                ((WithLp.toLp 2 :
                  Point3 → H3FourierPoint3) x)).re)) :=
        congrArg
          (fun f : ScalarField3 =>
            spatial3.d a (spatial3.d b f))
          hFirstEq
      _ =
        spatial3.d a
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv
              second
              ((WithLp.toLp 2 :
                Point3 → H3FourierPoint3) x)).re) :=
        congrArg
          (spatial3.d a)
          hSecondEq
      _ =
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            third
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)).re) :=
        hThirdEq

  have hBase :
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          N
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3 H := by
    rfl

  rw [← hBase]
  rw [hEq]

  exact hReal

/-- The repeated-index cubic selected velocity frontier needed by the
order-one temporal coefficient is automatic from the native H³ weight. -/
theorem h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed :
    H3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius := by
  intro E u T t₀ hNS ht₀ hE hTail
  intro q hq
  intro a k j

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

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
          U₀ hA hU₀ q y).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W q jf) := by
    funext y

    rw [← hAxisJ]

    simp only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      W
    ]

  rw [hComponent]

  dsimp only [W, U₀, hA, hU₀, jf]

  exact
    h3SelectedRestartRealVelocity_spatial_d_three_memLp2
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      hq.1
      hq.2
      (h3ClassicalizationFinOfAxis j)
      a k k

/-- With the cubic velocity mass now closed, the selected first-jet temporal
coefficient from the previous reduction belongs to physical `L²` outright. -/
theorem h3PreterminalSelectedFirstJetRelativeTemporalField_memLp_two_closed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq :
      q ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j a : PrimeTensor.Axis Depth.three) :
    MemLp
      (spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState
                  hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                r
                y).component j)
            q))
      2
      (volume : Measure Point3) := by
  exact
    h3PreterminalSelectedFirstJetRelativeTemporalField_memLp_two_of_repeatedThirdVelocityJet
      h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
      hNS ht₀ hE hTail hq j a

end

end Euclidean
end Bridge
end PrimeTensor
