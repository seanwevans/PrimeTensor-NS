import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Third.Velocity.L2.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Raw.Forcing.Physical.L2.Second

/-!
# Native H³ physical L² control of selected second velocity jets

The order-two Hilbert-space energy argument needs the selected second spatial
velocity jet as an actual physical `L²` state.

The cubic selected velocity theorem already proves the stronger third-jet
statement from the exact H³ spectral weight.  This file records the missing
quadratic radial baseline explicitly and transports two coordinate Fourier
multipliers back to physical space.

No positive-time smoothing gain is used: quadratic weight is native to H³.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform LineDeriv Topology
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedSecondVelocityL2Closure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedSecondVelocityL2Closure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The exact H³ Sobolev frequency weight dominates the unnormalized
quadratic radial weight. -/
theorem h3FourierNorm_sq_le_h3SobolevFrequencyWeight
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 2 ≤ h3SobolevFrequencyWeight ξ := by
  have h3 :
      ‖ξ‖ ^ 3 ≤ h3SobolevFrequencyWeight ξ :=
    h3FourierNorm_cubed_le_h3SobolevFrequencyWeight ξ

  by_cases h : ‖ξ‖ ≤ 1
  · have hWeightOne :
        (1 : ℝ) ≤ h3SobolevFrequencyWeight ξ :=
      one_le_h3SobolevFrequencyWeight ξ
    have hsq : ‖ξ‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg ξ]
    exact hsq.trans hWeightOne
  · have hOne : 1 < ‖ξ‖ := lt_of_not_ge h
    have hsq3 : ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 3 := by
      nlinarith [norm_nonneg ξ]
    exact hsq3.trans h3

/-- Quadratic radial weight times the inverse exact H³ weight is bounded by
one. -/
theorem h3FourierNorm_sq_mul_h3SobolevFrequencyWeightInv_le_one
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 2 * h3SobolevFrequencyWeightInv ξ ≤ 1 := by
  have hWeight :
      ‖ξ‖ ^ 2 ≤ h3SobolevFrequencyWeight ξ :=
    h3FourierNorm_sq_le_h3SobolevFrequencyWeight ξ

  have hInv0 :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact
      inv_nonneg.mpr
        (h3SobolevFrequencyWeight_pos ξ).le

  have hMul :=
    mul_le_mul_of_nonneg_right
      hWeight hInv0

  calc
    ‖ξ‖ ^ 2 * h3SobolevFrequencyWeightInv ξ
        ≤
      h3SobolevFrequencyWeight ξ *
        h3SobolevFrequencyWeightInv ξ :=
      hMul
    _ = 1 := by
      unfold h3SobolevFrequencyWeightInv
      exact
        mul_inv_cancel₀
          (ne_of_gt
            (h3SobolevFrequencyWeight_pos ξ))

/-- Every H³ spectral scalar state has quadratic radial raw Fourier `L²`. -/
theorem h3SpectralScalarRawFourier_quadraticWeight_memLp2
    (G : H3SpectralScalarState) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourier G ξ)
      2
      (volume : Measure H3FourierPoint3) := by
  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
            h3SpectralScalarRawFourier G ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (Complex.continuous_ofReal.comp
        (continuous_norm.pow 2)).aestronglyMeasurable.mul
        (h3SpectralScalarRawFourier_memLp2 G).1

  refine
    (MeasureTheory.Lp.memLp G).of_le
      hMeas
      ?_

  filter_upwards with ξ

  have hr2 :
      0 ≤ ‖ξ‖ ^ 2 :=
    pow_nonneg (norm_nonneg ξ) 2

  have hInv0 :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact
      inv_nonneg.mpr
        (h3SobolevFrequencyWeight_pos ξ).le

  have hMultiplier :
      ‖ξ‖ ^ 2 *
          h3SobolevFrequencyWeightInv ξ
        ≤
      1 :=
    h3FourierNorm_sq_mul_h3SobolevFrequencyWeightInv_le_one ξ

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hr2,
    h3SpectralScalarRawFourier,
    h3SobolevFrequencyWeightInvComplex,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hInv0
  ]

  calc
    ‖ξ‖ ^ 2 *
        (h3SobolevFrequencyWeightInv ξ * ‖G ξ‖)
        =
      (‖ξ‖ ^ 2 *
        h3SobolevFrequencyWeightInv ξ) *
        ‖G ξ‖ := by
          ring
    _ ≤ 1 * ‖G ξ‖ :=
      mul_le_mul_of_nonneg_right
        hMultiplier
        (norm_nonneg _)
    _ = ‖G ξ‖ := by
      rw [one_mul]

/-- Every ordered second spatial derivative of one selected real velocity
coordinate belongs to physical `L²` at a strict positive restart time. -/
theorem h3SelectedRestartRealVelocity_spatial_d_two_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (spatial3.d a
        (spatial3.d b
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W t i))))
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

  let af : Fin 3 :=
    h3ClassicalizationFinOfAxis a

  let bf : Fin 3 :=
    h3ClassicalizationFinOfAxis b

  let first : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol bf ξ * N ξ

  let second : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol af ξ *
        (h3FourierDerivativeSymbol bf ξ * N ξ)

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

  have hFirstInt :
      Integrable first
        (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) *
              (‖ξ‖ * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNFirstMoment.const_mul
        (2 * Real.pi)

    apply hDom.mono'
    · dsimp only [first, bf]
      exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis b)).aestronglyMeasurable.mul
          hNInt.aestronglyMeasurable
    · filter_upwards with ξ
      dsimp only [first, bf]
      rw [norm_mul]
      have hb :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis b) ξ
      unfold h3FourierGradientMagnitude at hb
      calc
        ‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ‖ *
            ‖N ξ‖
            ≤
          ((2 * Real.pi) * ‖ξ‖) *
            ‖N ξ‖ :=
          mul_le_mul_of_nonneg_right
            hb
            (norm_nonneg _)
        _ =
          (2 * Real.pi) *
            (‖ξ‖ * ‖N ξ‖) := by
          ring

  have hFirstMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖first ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hDom :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) *
              (‖ξ‖ ^ 2 * ‖N ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hNSecondMoment.const_mul
        (2 * Real.pi)

    apply hDom.mono'
    · exact
        continuous_norm.aestronglyMeasurable.mul
          hFirstInt.aestronglyMeasurable.norm
    · filter_upwards with ξ
      dsimp only [first, bf]

      have hLeftNonneg :
          0 ≤
            ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                N ξ‖ := by
        positivity

      have hRightNonneg :
          0 ≤
            (2 * Real.pi) *
              (‖ξ‖ ^ 2 * ‖N ξ‖) := by
        positivity

      have hb :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis b) ξ

      unfold h3FourierGradientMagnitude at hb

      have hBound :
          ‖ξ‖ *
              ‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ *
                N ξ‖
            ≤
          (2 * Real.pi) *
            (‖ξ‖ ^ 2 * ‖N ξ‖) := by
        rw [norm_mul]
        calc
          ‖ξ‖ *
              (‖h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis b) ξ‖ *
                ‖N ξ‖)
              ≤
            ‖ξ‖ *
              (((2 * Real.pi) * ‖ξ‖) *
                ‖N ξ‖) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hb
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
      hNSecondMoment.const_mul
        ((2 * Real.pi) ^ 2)

    apply hDom.mono'
    · dsimp only [second, af, bf]
      exact
        (h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis a)).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous
            (h3ClassicalizationFinOfAxis b)).aestronglyMeasurable.mul
            hNInt.aestronglyMeasurable)
    · filter_upwards with ξ
      dsimp only [second, af, bf]
      rw [norm_mul, norm_mul]

      have ha :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis a) ξ

      have hb :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          (h3ClassicalizationFinOfAxis b) ξ

      unfold h3FourierGradientMagnitude at ha hb

      calc
        ‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis a) ξ‖ *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis b) ξ‖ *
              ‖N ξ‖)
            ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (‖h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis b) ξ‖ *
              ‖N ξ‖) := by
          exact
            mul_le_mul_of_nonneg_right
              ha
              (mul_nonneg
                (norm_nonneg _)
                (norm_nonneg _))
        _ ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (((2 * Real.pi) * ‖ξ‖) *
              ‖N ξ‖) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                hb
                (norm_nonneg _))
              (by positivity)
        _ =
          (2 * Real.pi) ^ 2 *
            (‖ξ‖ ^ 2 * ‖N ξ‖) := by
          ring

  have hRadial :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 2 : ℝ) : ℂ) * N ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3SpectralScalarRawFourier_quadraticWeight_memLp2 H

  have hSecond2 :
      MemLp second
        2
        (volume : Measure H3FourierPoint3) := by
    refine
      hRadial.of_le_mul
        (c := (2 * Real.pi) ^ 2)
        hSecondInt.aestronglyMeasurable
        ?_

    filter_upwards with ξ

    dsimp only [second, af, bf]

    rw [norm_mul, norm_mul]

    have ha :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (h3ClassicalizationFinOfAxis a) ξ

    have hb :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (h3ClassicalizationFinOfAxis b) ξ

    have hGrad0 :
        0 ≤ h3FourierGradientMagnitude ξ := by
      unfold h3FourierGradientMagnitude
      positivity

    calc
      ‖h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ‖ *
          (‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ‖ *
            ‖N ξ‖)
          ≤
        h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ‖ *
            ‖N ξ‖) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg
              (norm_nonneg _)
              (norm_nonneg _))
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            ‖N ξ‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hb
              (norm_nonneg _))
            hGrad0
      _ =
        (2 * Real.pi) ^ 2 *
          ‖((‖ξ‖ ^ 2 : ℝ) : ℂ) * N ξ‖ := by
        unfold h3FourierGradientMagnitude
        rw [
          norm_mul,
          Complex.norm_real,
          Real.norm_eq_abs
        ]
        rw [
          abs_of_nonneg
            (pow_nonneg (norm_nonneg ξ) 2)
        ]
        ring

  have hComplex :
      MemLp
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            second
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x))
        2
        (volume : Measure Point3) :=
    memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedRawSecond
      hSecondInt hSecond2

  have hReal :
      MemLp
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            second
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)).re)
        2
        (volume : Measure Point3) :=
    memLp_re_of_memLp_complex_h3SelectedRawSecond
      hComplex

  have hFirstEq :
      spatial3.d b
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

    dsimp only [first, bf]

    exact
      fourierInv_re_onPoint3_spatialDerivative_eq_h3SelectedRawSecond
        hNInt hNFirstMoment b x

  have hSecondEq :
      spatial3.d a
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

    dsimp only [second, first, af]

    exact
      fourierInv_re_onPoint3_spatialDerivative_eq_h3SelectedRawSecond
        hFirstInt hFirstMoment a x

  have hEq :
      spatial3.d a
        (spatial3.d b
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv
              N
              ((WithLp.toLp 2 :
                Point3 → H3FourierPoint3) x)).re))
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          second
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re) := by
    calc
      spatial3.d a
        (spatial3.d b
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv
              N
              ((WithLp.toLp 2 :
                Point3 → H3FourierPoint3) x)).re))
          =
        spatial3.d a
          (fun x : Point3 =>
            (FourierTransformInv.fourierInv
              first
              ((WithLp.toLp 2 :
                Point3 → H3FourierPoint3) x)).re) :=
        congrArg
          (spatial3.d a)
          hFirstEq
      _ =
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            second
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)).re) :=
        hSecondEq

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

end

end Euclidean
end Bridge
end PrimeTensor
