import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Physical.L2.Zero
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Heat.First.Derivative.Endpoint
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Heat.Second.Derivative.Endpoint
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Heat.Third.Derivative.Endpoint
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Third.Mixed.Derivative.Candidate.Bridge

/-!
# Physical L² spatial jet for selected Leray forcing

The zero-order physical reconstruction is already in `L²`.  At every strict
positive selected restart time the raw Leray forcing also has arbitrary radial
Fourier `L²` weight.  One, two, and three coordinate derivative symbols are
bounded by the corresponding radial weights, hence their zero-lag coordinate
amplitudes belong to Fourier `L²`.

The existing endpoint classicalization identifies the inverse Fourier
reconstructions of those amplitudes with the genuine first, second, and third
Fréchet derivatives of the instantaneous forcing.  Existing real/Euclidean
bridges then identify their real parts with the concrete ordered `spatial3.d`
fields.

Thus every ordered physical derivative of the selected real Leray forcing
through order three belongs to `L²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingPhysicalL2Jet
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedForcingPhysicalL2Jet :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic Plancherel and real-part helpers -/

private theorem memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedForcingJet
    {f : H3FourierPoint3 → ℂ}
    (hf1 :
      Integrable f
        (volume : Measure H3FourierPoint3))
    (hf2 :
      MemLp f 2
        (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
      2
      (volume : Measure Point3) := by

  let f2 : H3FourierComplexL2 :=
    hf2.toLp f

  let u2 : H3FourierComplexL2 :=
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm f2

  let p2 :
      MeasureTheory.Lp
        ℂ
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.compMeasurePreserving
      (WithLp.toLp 2 : Point3 → H3FourierPoint3)
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three))
      u2

  have hCompat :
      FourierTransformInv.fourierInv f
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2]
    exact
      h3FourierInv_integrable_memLp2_ae_eq_L2
        hf1 hf2

  have hComp :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
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

  have hFrom :
      ((p2 :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure Point3)) :
        Point3 → ℂ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((u2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    dsimp only [p2]
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        u2
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hAE :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      ((p2 :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure Point3)) :
        Point3 → ℂ) :=
    hComp.trans hFrom.symm

  have hp2 :
      MemLp
        ((p2 :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure Point3)) :
          Point3 → ℂ)
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.memLp p2

  exact
    (memLp_congr_ae hAE).2 hp2

private theorem memLp_re_of_memLp_complex_h3SelectedForcingJet
    {f : Point3 → ℂ}
    (hf :
      MemLp f 2
        (volume : Measure Point3)) :
    MemLp
      (fun x : Point3 => (f x).re)
      2
      (volume : Measure Point3) := by

  let F :
      MeasureTheory.Lp
        ℂ
        2
        (volume : Measure Point3) :=
    hf.toLp f

  let R :
      MeasureTheory.Lp
        ℝ
        2
        (volume : Measure Point3) :=
    Complex.reCLM.compLp F

  have hF :
      ((F :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure Point3)) :
        Point3 → ℂ)
        =ᵐ[(volume : Measure Point3)]
      f := by
    dsimp only [F]
    exact MeasureTheory.MemLp.coeFn_toLp hf

  have hR :
      ((R :
          MeasureTheory.Lp
            ℝ
            2
            (volume : Measure Point3)) :
        Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (((F :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure Point3)) :
          Point3 → ℂ) x).re) := by
    dsimp only [R]
    exact Complex.reCLM.coeFn_compLp F

  have hAE :
      (fun x : Point3 => (f x).re)
        =ᵐ[(volume : Measure Point3)]
      ((R :
          MeasureTheory.Lp
            ℝ
            2
            (volume : Measure Point3)) :
        Point3 → ℝ) := by
    filter_upwards [hF, hR] with x hxF hxR
    calc
      (f x).re
          =
        (((F :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure Point3)) :
          Point3 → ℂ) x).re :=
        congrArg Complex.re hxF.symm
      _ =
        ((R :
            MeasureTheory.Lp
              ℝ
              2
              (volume : Measure Point3)) :
          Point3 → ℝ) x :=
        hxR.symm

  have hRMem :
      MemLp
        ((R :
            MeasureTheory.Lp
              ℝ
              2
              (volume : Measure Point3)) :
          Point3 → ℝ)
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.memLp R

  exact
    (memLp_congr_ae hAE).2 hRMem

/-! ## Fourier L² coordinate amplitudes -/

private theorem h3SelectedRestartForcing_firstCoordinate_memLp2
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

  have hTwoPi : 0 ≤ 2 * Real.pi := by
    positivity

  rw [norm_mul]
  have hDeriv :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ * ‖N ξ‖
        ≤
      ((2 * Real.pi) * ‖ξ‖) * ‖N ξ‖ := by
        unfold h3FourierGradientMagnitude at hDeriv
        exact
          mul_le_mul_of_nonneg_right
            hDeriv
            (norm_nonneg _)
    _ =
      (2 * Real.pi) *
        ‖((‖ξ‖ ^ 1 : ℝ) : ℂ) * N ξ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp only [pow_one, abs_of_nonneg (norm_nonneg ξ)]
      ring

private theorem h3SelectedRestartForcing_secondCoordinate_memLp2
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

  have hGrad0 : 0 ≤ h3FourierGradientMagnitude ξ := by
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

private theorem h3SelectedRestartForcing_thirdCoordinate_memLp2
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

  have hGrad0 : 0 ≤ h3FourierGradientMagnitude ξ := by
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

/-! ## Physical first, second, and third derivative L² -/

/-- Every first spatial derivative of the real selected Leray forcing belongs
 to physical `L²`. -/
theorem h3SelectedRestartRealLerayForcing_spatial_d_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (spatial3.d a
        (fun x : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W t) (W t) i x).re))
      2
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let af : Fin 3 :=
    h3ClassicalizationFinOfAxis a

  let raw : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol af ξ *
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i ξ

  have hRawInt :
      Integrable raw
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, af, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_derivative_integrable
        hν U₀ hA hU₀ ht htR.le i
        (h3ClassicalizationFinOfAxis a)

  have hRaw2 :
      MemLp raw 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, af, W]
    exact
      h3SelectedRestartForcing_firstCoordinate_memLp2
        hν U₀ hA hU₀ ht htR.le i
        (h3ClassicalizationFinOfAxis a)

  have hComplex :
      MemLp
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            raw
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        2
        (volume : Measure Point3) :=
    memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedForcingJet
      hRawInt hRaw2

  have hReal :
      MemLp
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            raw
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        2
        (volume : Measure Point3) :=
    memLp_re_of_memLp_complex_h3SelectedForcingJet
      hComplex

  have hEq :
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      spatial3.d a
        (fun x : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W t) (W t) i x).re) := by
    funext x

    have hEndpoint :=
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_zero_eq_selectedRestart_fderiv_apply
        hν U₀ hA hU₀ ht htR.le i af
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

    have hPhysical :=
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_eq_re_fderiv
        hν U₀ hA hU₀ ht htR i x a

    have hInvEq :
        FourierTransformInv.fourierInv
            raw
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
          =
        (fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
          (h3FourierAxisDirection a) := by
      dsimp only at hEndpoint
      unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative at hEndpoint
      rw [
        h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
          ν (W t) (W t) i
      ] at hEndpoint
      simpa only [
        raw, af, W,
        h3AxisOfFin3_h3ClassicalizationFinOfAxis
      ] using hEndpoint

    calc
      (FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
          =
        ((fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
          (h3FourierAxisDirection a)).re :=
        congrArg Complex.re hInvEq
      _ =
        spatial3.d a
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W t) (W t) i y).re)
          x := hPhysical.symm

  rw [← hEq]
  exact hReal

/-- Every ordered second spatial derivative of the real selected Leray forcing
 belongs to physical `L²`. -/
theorem h3SelectedRestartRealLerayForcing_spatial_d_two_memLp2
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
          (fun x : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W t) (W t) i x).re)))
      2
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let af : Fin 3 := h3ClassicalizationFinOfAxis a
  let bf : Fin 3 := h3ClassicalizationFinOfAxis b

  let raw : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol af ξ *
        (h3FourierDerivativeSymbol bf ξ *
          h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ)

  have hRawInt :
      Integrable raw
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, af, bf, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondCoordinate_integrable
        hν U₀ hA hU₀ ht htR.le i
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)

  have hRaw2 :
      MemLp raw 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, af, bf, W]
    exact
      h3SelectedRestartForcing_secondCoordinate_memLp2
        hν U₀ hA hU₀ ht htR.le i
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)

  have hComplex :=
    memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedForcingJet
      hRawInt hRaw2

  have hReal :=
    memLp_re_of_memLp_complex_h3SelectedForcingJet
      hComplex

  have hEq :
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      spatial3.d a
        (spatial3.d b
          (fun x : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W t) (W t) i x).re)) := by
    funext x

    have hEndpoint :=
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
        hν U₀ hA hU₀ ht htR.le i af bf
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

    have hPhysical :=
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_two_eq_re_secondFrechet
        hν U₀ hA hU₀ ht htR i x a b

    have hInvEq :
        FourierTransformInv.fourierInv
            raw
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
          =
        iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
          ![
            h3FourierAxisDirection a,
            h3FourierAxisDirection b
          ] := by
      dsimp only at hEndpoint
      unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative at hEndpoint
      unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude at hEndpoint
      rw [
        h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
          ν (W t) (W t) i
      ] at hEndpoint
      simpa only [
        raw, af, bf, W,
        h3AxisOfFin3_h3ClassicalizationFinOfAxis
      ] using hEndpoint

    calc
      (FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
          =
        (iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
          ![
            h3FourierAxisDirection a,
            h3FourierAxisDirection b
          ]).re :=
        congrArg Complex.re hInvEq
      _ =
        spatial3.d a
          (spatial3.d b
            (fun y : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W t) (W t) i y).re))
          x := hPhysical.symm

  rw [← hEq]
  exact hReal

/-- Every ordered third spatial derivative of the real selected Leray forcing
 belongs to physical `L²`. -/
theorem h3SelectedRestartRealLerayForcing_spatial_d_three_memLp2
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
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W t) (W t) i x).re))))
      2
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let af : Fin 3 := h3ClassicalizationFinOfAxis a
  let bf : Fin 3 := h3ClassicalizationFinOfAxis b
  let cf : Fin 3 := h3ClassicalizationFinOfAxis c

  let raw : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol af ξ *
        (h3FourierDerivativeSymbol bf ξ *
          (h3FourierDerivativeSymbol cf ξ *
            h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ))

  have hRawInt :
      Integrable raw
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, af, bf, cf, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdCoordinate_integrable
        hν U₀ hA hU₀ ht htR.le i
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)
        (h3ClassicalizationFinOfAxis c)

  have hRaw2 :
      MemLp raw 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, af, bf, cf, W]
    exact
      h3SelectedRestartForcing_thirdCoordinate_memLp2
        hν U₀ hA hU₀ ht htR.le i
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)
        (h3ClassicalizationFinOfAxis c)

  have hComplex :=
    memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedForcingJet
      hRawInt hRaw2

  have hReal :=
    memLp_re_of_memLp_complex_h3SelectedForcingJet
      hComplex

  have hEq :
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)
        =
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (fun x : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W t) (W t) i x).re))) := by
    funext x

    have hEndpoint :=
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
        hν U₀ hA hU₀ ht htR.le i af bf cf
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

    have hPhysical :=
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_three_eq_re_thirdFrechet
        hν U₀ hA hU₀ ht htR i x a b c

    have hInvEq :
        FourierTransformInv.fourierInv
            raw
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
          =
        iteratedFDeriv ℝ 3
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
          ![
            h3FourierAxisDirection a,
            h3FourierAxisDirection b,
            h3FourierAxisDirection c
          ] := by
      dsimp only at hEndpoint
      unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative at hEndpoint
      unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude at hEndpoint
      rw [
        h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
          ν (W t) (W t) i
      ] at hEndpoint
      simpa only [
        raw, af, bf, cf, W,
        h3AxisOfFin3_h3ClassicalizationFinOfAxis
      ] using hEndpoint

    calc
      (FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
          =
        (iteratedFDeriv ℝ 3
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
          ![
            h3FourierAxisDirection a,
            h3FourierAxisDirection b,
            h3FourierAxisDirection c
          ]).re :=
        congrArg Complex.re hInvEq
      _ =
        spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (fun y : Point3 =>
                (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                  (W t) (W t) i y).re)))
          x := hPhysical.symm

  rw [← hEq]
  exact hReal

/-- Complete physical `L²` jet through order three for one selected Leray
forcing coordinate at a strict positive restart time. -/
theorem h3SelectedRestartRealLerayForcing_jet_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let F : ScalarField3 :=
      fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i x).re
    MemLp F 2 (volume : Measure Point3)
      ∧
    (∀ a : PrimeTensor.Axis Depth.three,
      MemLp (spatial3.d a F) 2 (volume : Measure Point3))
      ∧
    (∀ a b : PrimeTensor.Axis Depth.three,
      MemLp
        (spatial3.d a (spatial3.d b F))
        2
        (volume : Measure Point3))
      ∧
    (∀ a b c : PrimeTensor.Axis Depth.three,
      MemLp
        (spatial3.d a
          (spatial3.d b
            (spatial3.d c F)))
        2
        (volume : Measure Point3)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : ScalarField3 :=
    fun x : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i x).re

  refine ⟨?_, ?_, ?_, ?_⟩

  · exact
      h3SelectedRestartRealLerayForcing_memLp2
        (s := t) hν U₀ hA hU₀ i

  · intro a
    exact
      h3SelectedRestartRealLerayForcing_spatial_d_memLp2
        hν U₀ hA hU₀ ht htR i a

  · intro a b
    exact
      h3SelectedRestartRealLerayForcing_spatial_d_two_memLp2
        hν U₀ hA hU₀ ht htR i a b

  · intro a b c
    exact
      h3SelectedRestartRealLerayForcing_spatial_d_three_memLp2
        hν U₀ hA hU₀ ht htR i a b c

end

end Euclidean
end Bridge
end PrimeTensor
