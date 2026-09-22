import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedRawForcingThirdMoment
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedRawForcingPhysicalL2Second

/-!
# Third physical L² derivative of the selected raw forcing

The unprojected selected forcing now has an integrable cubic Fourier moment and
Fourier `L²` control after every ordered triple of coordinate multipliers.

The generic one-coordinate inverse-Fourier derivative bridge from the order-two
closure is reused three times.  The cubic radial moment controls the first
radial moment of the two-coordinate multiplier, so the third differentiation
is legitimate in the ordinary inverse-Fourier representation.  Plancherel and
real projection then give the physical `L²` conclusion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform LineDeriv Topology

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedRawForcingPhysicalL2Third
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedRawForcingPhysicalL2Third :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every ordered third spatial derivative of the real selected raw forcing
belongs to physical `L²`. -/
theorem h3SelectedRestartRealRawForcing_spatial_d_three_memLp2
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
            (fun x : Point3 =>
              (FourierTransformInv.fourierInv
                (h3RawFinOuterProductDivergence
                  (W t) (W t) i)
                ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re))))
      2
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinOuterProductDivergence (W t) (W t) i

  let af : Fin 3 := h3ClassicalizationFinOfAxis a
  let bf : Fin 3 := h3ClassicalizationFinOfAxis b
  let cf : Fin 3 := h3ClassicalizationFinOfAxis c

  let first : H3FourierPoint3 → ℂ :=
    fun ξ => h3FourierDerivativeSymbol cf ξ * N ξ

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
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact h3RawFinOuterProductDivergence_integrable (W t) (W t) i

  have hNFirstMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR.le i

  have hNSecondMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 2 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR.le i

  have hNThirdMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 3 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR.le i

  have hFirstInt :
      Integrable first (volume : Measure H3FourierPoint3) := by
    dsimp only [first, cf]
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) * (‖ξ‖ * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNFirstMoment.const_mul (2 * Real.pi)

    apply hDom.mono'
    · exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis c)).aestronglyMeasurable.mul
          hNInt.aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul]
      have hDeriv :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ
      unfold h3FourierGradientMagnitude at hDeriv
      calc
        ‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis c) ξ‖ * ‖N ξ‖
            ≤
          ((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖ :=
          mul_le_mul_of_nonneg_right hDeriv (norm_nonneg _)
        _ =
          (2 * Real.pi) * (‖ξ‖ * ‖N ξ‖) := by ring

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
      dsimp only [first, cf]

      have hLeftNonneg :
          0 ≤
            ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ * N ξ‖ := by
        positivity

      have hRightNonneg :
          0 ≤
            (2 * Real.pi) * (‖ξ‖ ^ 2 * ‖N ξ‖) := by
        positivity

      have hDeriv :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis c) ξ
      unfold h3FourierGradientMagnitude at hDeriv

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
                (mul_le_mul_of_nonneg_right hDeriv (norm_nonneg _))
                (norm_nonneg ξ)
          _ =
            (2 * Real.pi) * (‖ξ‖ ^ 2 * ‖N ξ‖) := by ring

      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeftNonneg,
        abs_of_nonneg hRightNonneg
      ] using hBound

  have hSecondInt :
      Integrable second (volume : Measure H3FourierPoint3) := by
    dsimp only [second, bf, cf, N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_secondCoordinate_integrable
        hν U₀ hA hU₀ ht htR.le i
        (h3ClassicalizationFinOfAxis b)
        (h3ClassicalizationFinOfAxis c)

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
      dsimp only [second, bf, cf]

      have hLeftNonneg :
          0 ≤
            ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ * N ξ)‖ := by
        positivity

      have hRightNonneg :
          0 ≤
            (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 3 * ‖N ξ‖) := by
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
                  hb
                  (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
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
          _ =
            (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 3 * ‖N ξ‖) := by ring

      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hLeftNonneg,
        abs_of_nonneg hRightNonneg
      ] using hBound

  have hThirdInt :
      Integrable third (volume : Measure H3FourierPoint3) := by
    dsimp only [third, af, bf, cf, N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_thirdCoordinate_integrable
        hν U₀ hA hU₀ ht htR.le i
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)
        (h3ClassicalizationFinOfAxis c)

  have hThird2 :
      MemLp third 2 (volume : Measure H3FourierPoint3) := by
    dsimp only [third, af, bf, cf, N, W]
    exact
      h3SelectedRestartRawForcing_thirdCoordinate_memLp2
        hν U₀ hA hU₀ ht htR.le i
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)
        (h3ClassicalizationFinOfAxis c)

  have hComplex :
      MemLp
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            third
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        2
        (volume : Measure Point3) :=
    memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedRawSecond
      hThirdInt hThird2

  have hReal :
      MemLp
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            third
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        2
        (volume : Measure Point3) :=
    memLp_re_of_memLp_complex_h3SelectedRawSecond hComplex

  have hFirstEq :
      spatial3.d c
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv
              N
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          first
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
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
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          second
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
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
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          third
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
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
                ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)))
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          third
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    calc
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (fun x : Point3 =>
              (FourierTransformInv.fourierInv
                N
                ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)))
          =
        spatial3.d a
          (spatial3.d b
            (fun x : Point3 =>
              (FourierTransformInv.fourierInv
                first
                ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)) :=
        congrArg
          (fun f : ScalarField3 => spatial3.d a (spatial3.d b f))
          hFirstEq
      _ =
        spatial3.d a
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv
              second
              ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) :=
        congrArg (spatial3.d a) hSecondEq
      _ =
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            third
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) :=
        hThirdEq

  rw [hEq]
  exact hReal

end

end Euclidean
end Bridge
end PrimeTensor
